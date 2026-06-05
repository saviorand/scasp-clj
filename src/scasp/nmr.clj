(ns scasp.nmr
  "Call graph analysis and NMR (Non-monotonic Reasoning) check generation.

   Detects odd loops over negation (OLON) in the program and generates
   auxiliary sub-check predicates that are appended to every query."
  (:require [scasp.term    :as term]
            [scasp.program :as prog]
            [scasp.duals   :as duals]))

;;; ── Call graph ───────────────────────────────────────────────────────────────

(defn build-call-graph
  "Build a map {functor → #{called-functors}} from program rules.
   Edges only go from positive predicates; negated calls are to dual functors."
  [program]
  (let [all-rules (for [[f rs] (:rules program) r rs] [f r])]
    (reduce (fn [g [f {:keys [body]}]]
              (let [called (for [goal body
                                 :let [gf (prog/goal-functor goal)]
                                 :when gf]
                             gf)]
                (update g f (fn [s] (into (or s #{}) called)))))
            {}
            all-rules)))

;;; ── SCC detection (Tarjan's algorithm) ──────────────────────────────────────

(defn- tarjan-sccs
  "Return a list of strongly connected components (each a set of nodes)."
  [graph]
  (let [nodes (set (concat (keys graph) (mapcat val graph)))
        state (atom {:index 0 :stack [] :on-stack #{} :indices {} :lowlinks {} :sccs []})
        strongconnect
        (fn strongconnect [v]
          (let [{:keys [index]} @state]
            (swap! state assoc-in [:indices v] index)
            (swap! state assoc-in [:lowlinks v] index)
            (swap! state update :index inc)
            (swap! state update :stack conj v)
            (swap! state update :on-stack conj v))
          (doseq [w (get graph v #{})]
            (if (nil? (get-in @state [:indices w]))
              (do (strongconnect w)
                  (let [lv (get-in @state [:lowlinks v])
                        lw (get-in @state [:lowlinks w])]
                    (when (< lw lv)
                      (swap! state assoc-in [:lowlinks v] lw))))
              (when (contains? (:on-stack @state) w)
                (let [lv  (get-in @state [:lowlinks v])
                      iw  (get-in @state [:indices w])]
                  (when (< iw lv)
                    (swap! state assoc-in [:lowlinks v] iw))))))
          (when (= (get-in @state [:lowlinks v])
                   (get-in @state [:indices v]))
            (loop [scc #{}]
              (let [w (peek (:stack @state))]
                (swap! state update :stack pop)
                (swap! state update :on-stack disj w)
                (let [scc' (conj scc w)]
                  (if (= w v)
                    (swap! state update :sccs conj scc')
                    (recur scc')))))))]
    (doseq [v nodes]
      (when (nil? (get-in @state [:indices v]))
        (strongconnect v)))
    (:sccs @state)))

;;; ── OLON detection ───────────────────────────────────────────────────────────

(defn- neg-count-in-body
  "Number of NAF (or dual) goals in rule body."
  [{:keys [body]}]
  (count (filter (fn [g]
                   (or (term/is-naf? g)
                       (and (term/is-compound? g) (term/is-dual? (term/term-functor g)))))
                 body)))

(defn olon-rules
  "Return rules that participate in odd loops over negation.
   Excludes _false/0 headless rules — they are always added to the NMR check
   separately as integrity constraint sub-checks."
  [program]
  (let [cg   (build-call-graph program)
        sccs (tarjan-sccs cg)
        cyclic-sccs (filter (fn [scc]
                              (or (> (count scc) 1)
                                  (contains? (get cg (first scc) #{}) (first scc))))
                            sccs)]
    (into []
          (for [scc  cyclic-sccs
                f    scc
                :when (not= f "_false/0")   ; headless rules handled separately
                r    (prog/defined-rules f program)
                :when (pos? (neg-count-in-body r))]
            r))))

;;; ── Integrity constraint sub-checks ─────────────────────────────────────────

(defn- gen-integrity-chks
  "For each _false/0 rule (integrity constraint :- Body), create a sub-check
   predicate _chk_0_N with that body, compile its dual, and return
   [updated-prog  [not(_chk_0_1), not(_chk_0_2), …]] — one NAF goal per constraint.

   Mirrors the reference olon_chks handling for _false_0 rules:
     - creates _chk_0_N :- Body
     - compiles dual for _chk_0_N via comp-dual
     - adds not(_chk_0_N) to NMR goals
     - asserts trivial fact not__false() as a placeholder"
  [prog start-n]
  (let [false-rules (prog/defined-rules "_false/0" prog)
        ;; Assert trivial not__false/0 fact (placeholder; real checks are via _chk_0_N)
        not-false-fact (prog/make-rule (term/make-compound "not__false" []) [])
        prog' (prog/assert-rule not-false-fact prog)]
    (reduce
     (fn [[p goals n] constraint-rule]
       (let [chk-name (str "_chk_0_" n)
             chk-head (term/make-compound chk-name [])
             ;; _chk_0_N :- <constraint body>
             chk-rule (prog/make-rule chk-head (:body constraint-rule))
             p'       (prog/assert-rule chk-rule p)
             ;; compile dual for _chk_0_N
             p''      (duals/comp-dual (str chk-name "/0")
                                       (prog/defined-rules (str chk-name "/0") p')
                                       p')
             ;; not(_chk_0_N) goal for NMR check
             naf-goal {:op :not :args [chk-head]}]
         [p'' (conj goals naf-goal) (inc n)]))
     [prog' [] start-n]
     false-rules)))

;;; ── NMR sub-check predicates ─────────────────────────────────────────────────

(defn- gen-olon-chk
  "Generate a sub-check rule for a single OLON rule.
   The sub-check calls the dual of the rule's head."
  [olon-rule chk-n]
  (let [head      (:head olon-rule)
        df        (term/negate-functor (term/term-functor head))
        dual-args (prog/var-list (term/functor-arity df))
        dual-call (term/make-compound (term/functor-name-str df) dual-args)
        chk-head  (term/make-compound (str "_chk" chk-n) [])
        chk-body  [dual-call]]
    (prog/make-rule chk-head chk-body)))

;;; ── generate-nmr-check entry point ──────────────────────────────────────────

(defn generate-nmr-check
  "Generate NMR check goals and rules.  Returns updated program."
  [prog]
  (let [olon (olon-rules prog)
        ;; Integrity constraint sub-checks (one per _false/0 rule)
        [prog-with-integrity integrity-goals _]
        (gen-integrity-chks prog (inc (count olon)))]
    (if (empty? olon)
      ;; No OLONs → NMR check is just _nmr_check/0 (a trivial fact)
      (let [nmr-head  (term/make-compound "_nmr_check" [])
            prog'     (prog/assert-rule (prog/make-rule nmr-head []) prog-with-integrity)
            nmr-goals (into [(term/make-compound "_nmr_check" [])] integrity-goals)]
        (prog/assert-nmr-check nmr-goals prog'))
      ;; Generate sub-checks for OLON rules
      (let [chk-rules (map-indexed (fn [i r] (gen-olon-chk r (inc i))) olon)
            chk-goals (mapv (fn [i] (term/make-compound (str "_chk" (inc i)) [])) (range (count olon)))
            nmr-head  (term/make-compound "_nmr_check" [])
            nmr-rule  (prog/make-rule nmr-head chk-goals)
            prog'     (reduce #(prog/assert-rule %2 %1) prog-with-integrity chk-rules)
            prog''    (prog/assert-rule nmr-rule prog')
            nmr-goals (into [(term/make-compound "_nmr_check" [])] integrity-goals)]
        (prog/assert-nmr-check nmr-goals prog'')))))
