(ns scasp.nmr
  "Call graph analysis and NMR (Non-monotonic Reasoning) check generation.

   Detects odd loops over negation (OLON) in the program and generates
   auxiliary sub-check predicates that are appended to every query.

   Algorithm mirrors nmr_check.pl / call_graph.pl from refs/scasp:
   - Build the call graph from *original user rules only* (no duals, no
     generated _chk / _nmr_check predicates).
   - Use DFS with per-path negation counting to classify each cycle.
   - Only cycles with an odd total negation count are OLONs."
  (:require [clojure.string :as str]
            [scasp.term    :as term]
            [scasp.program :as prog]))

;;; ── User-rule filter ─────────────────────────────────────────────────────────

(defn- user-functor?
  "True for functors that belong to the original user program.
   Excludes duals (not_*), inner duals (_not_*), NMR/chk helpers (_*),
   and headless-rule dummy heads."
  [f]
  (and (not (term/is-dual? f))
       (not (prog/headless-functor? f))
       (not (prog/scasp-builtin? f))
       (not (str/starts-with? (term/functor-name-str f) "_"))))

;;; ── Call graph (user rules only) ─────────────────────────────────────────────

(defn- build-user-call-graph
  "Build a map {functor → [{:to called-functor :neg? bool} …]} from user rules.
   :neg? true when the call is negated (NAF or explicit dual call)."
  [program]
  (reduce (fn [g [f {:keys [body]}]]
            (let [edges (for [goal body
                               :let [gf   (prog/goal-functor goal)
                                     neg? (or (term/is-naf? goal)
                                              (term/is-sneg? goal))]
                               :when (and gf (user-functor? (term/negate-functor gf)))
                               ;; resolve to the positive functor name
                               :let [pos-f (if (term/is-dual? gf)
                                             (term/negate-functor gf)
                                             gf)]]
                           {:to pos-f :neg? neg?})]
              (update g f (fn [es] (into (or es []) edges)))))
          {}
          (for [[f rs] (:rules program)
                :when  (user-functor? f)
                r      rs]
            [f r])))

;;; ── Path-based DFS cycle detection ──────────────────────────────────────────

(defn- update-neg
  "Same as neg_value in the reference: 0 + neg → 1; 1 + neg → 2; 2 + neg → 1."
  [n neg?]
  (if-not neg?
    n
    (case n
      0 1
      1 2
      2 1)))

(defn- dfs-from
  "DFS from node `start` collecting OLON rule-functors.
   visited is a set of [node parity] pairs to avoid revisiting.
   path is the ordered list of [from neg?] edges on the current path.
   Returns a set of functors that are part of OLON cycles."
  [start graph]
  (let [olon-nodes (atom #{})]
    (letfn [(visit [node neg-parity path-nodes visited]
              (doseq [{:keys [to neg?]} (get graph node [])]
                (let [new-parity (update-neg neg-parity neg?)]
                  (cond
                    ;; Cycle back to a node already on the current path
                    (contains? path-nodes to)
                    (when (= new-parity 1) ; odd negation count → OLON
                      ;; Mark every node in the cycle as OLON
                      (swap! olon-nodes conj to)
                      (swap! olon-nodes conj node))

                    ;; Already visited this node with this parity → skip
                    (contains? visited [to new-parity])
                    nil

                    ;; New node: recurse
                    :else
                    (visit to new-parity
                           (conj path-nodes to)
                           (conj visited [to new-parity]))))))]
      (visit start 0 #{start} #{[start 0]}))
    @olon-nodes))

;;; ── OLON detection ───────────────────────────────────────────────────────────

(defn olon-rules
  "Return original user rules whose head functor participates in an odd loop
   over negation.  Excludes _false/0 headless rules (handled by DCC)."
  [program]
  (let [cg         (build-user-call-graph program)
        all-nodes  (set (concat (keys cg) (map :to (mapcat val cg))))
        olon-nodes (reduce (fn [acc node]
                             (into acc (dfs-from node cg)))
                           #{}
                           all-nodes)]
    (into []
          (for [f    olon-nodes
                :when (user-functor? f)
                :when (not= f "_false/0")
                r    (prog/defined-rules f program)]
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
   not by NMR sub-checks, so they are not added to nmr-goals here.

   opts:
     :no-olon  true → skip OLON detection; treat program as having no OLONs
     :no-nmr   true → skip NMR check entirely; append no NMR goals to queries"
  ([prog] (generate-nmr-check prog {}))
  ([prog opts]
   (if (:no-nmr opts)
     (prog/assert-nmr-check [] prog)
     (let [olon (if (:no-olon opts) [] (olon-rules prog))]
       (if (empty? olon)
         (let [nmr-head  (term/make-compound "_nmr_check" [])
               prog'     (prog/assert-rule (prog/make-rule nmr-head []) prog)
               nmr-goals [(term/make-compound "_nmr_check" [])]]
           (prog/assert-nmr-check nmr-goals prog'))
         (let [chk-rules (map-indexed (fn [i r] (gen-olon-chk r (inc i))) olon)
               chk-goals (mapv (fn [i] (term/make-compound (str "_chk" (inc i)) [])) (range (count olon)))
               nmr-head  (term/make-compound "_nmr_check" [])
               nmr-rule  (prog/make-rule nmr-head chk-goals)
               prog'     (reduce #(prog/assert-rule %2 %1) prog chk-rules)
               prog''    (prog/assert-rule nmr-rule prog')
               nmr-goals [(term/make-compound "_nmr_check" [])]]
           (prog/assert-nmr-check nmr-goals prog'')))))))
