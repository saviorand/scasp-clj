(ns scasp.nmr
  "Call graph analysis and NMR (Non-monotonic Reasoning) check generation.

   Detects odd loops over negation (OLON) in the program and generates
   auxiliary sub-check predicates that are appended to every query."
  (:require [scasp.term    :as term]
            [scasp.program :as prog]))

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
  "Generate NMR check goals and rules.  Returns updated program.
   Integrity constraints (_false/0 rules) are handled by DCC in run-query,
   not by NMR sub-checks, so they are not added to nmr-goals here."
  [prog]
  (let [olon (olon-rules prog)]
    (if (empty? olon)
      ;; No OLONs → NMR check is just _nmr_check/0 (a trivial fact)
      (let [nmr-head  (term/make-compound "_nmr_check" [])
            prog'     (prog/assert-rule (prog/make-rule nmr-head []) prog)
            nmr-goals [(term/make-compound "_nmr_check" [])]]
        (prog/assert-nmr-check nmr-goals prog'))
      ;; Generate sub-checks for OLON rules
      (let [chk-rules (map-indexed (fn [i r] (gen-olon-chk r (inc i))) olon)
            chk-goals (mapv (fn [i] (term/make-compound (str "_chk" (inc i)) [])) (range (count olon)))
            nmr-head  (term/make-compound "_nmr_check" [])
            nmr-rule  (prog/make-rule nmr-head chk-goals)
            prog'     (reduce #(prog/assert-rule %2 %1) prog chk-rules)
            prog''    (prog/assert-rule nmr-rule prog')
            nmr-goals [(term/make-compound "_nmr_check" [])]]
        (prog/assert-nmr-check nmr-goals prog'')))))
