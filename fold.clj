(ns fold
  "FOLD-R ILP algorithm — pure Clojure port of tools/code-tool/scasp/fold.pl.

   Learns defeasible Horn clauses from positive/negative examples and
   propositionalized background knowledge. Output is in scasp-clj term
   format and can be passed directly to scasp.main/solve-all.

   Background must be propositionalized: all predicates unary, stored as
     {pred-kw #{example-kw ...}}

   Positive/negative examples are keyword seqs: [:b1 :b2 ...]

   Example — beans domain:
     (induce :white [:b1] []
             {:bean #{:b1} :from_s1 #{:b1}}
             [:bean :from_s1])
     ;=> {:positive-rules
     ;     [{:head {:op :white :args [\"X\"]}
     ;       :body [{:op :bean :args [\"X\"]}]}]
     ;    :exception-rules []}

   Exception predicates are named :ab0, :ab1, ... and appear as
   {:op :not :args [{:op :ab0 :args [\"X\"]}]} in the positive rule bodies,
   realising s(CASP) default logic.

   Design note: the solver state carries the background map (:bg) so that
   newly learned exception rules can be materialised into it and subsequent
   coverage checks see (not ab_N(X)) evaluate correctly — matching the
   Prolog version's asserta/retract semantics.")

;;; ── Coverage ──────────────────────────────────────────────────────────────────

(defn- satisfies?
  "True when example satisfies every literal in body against background.
   Handles three literal forms:
     {:op :pred ...}                   — plain fact lookup
     {:op :not :args [{:op :pred}]}    — NAF: fact must be absent
     {:op :member :args [_ #{...}]}    — set membership (enumerate fallback)"
  [body example background]
  (every?
   (fn [lit]
     (case (:op lit)
       :not    (let [inner (first (:args lit))]
                 (not (contains? (get background (:op inner) #{}) example)))
       :member (contains? (second (:args lit)) example)
       (contains? (get background (:op lit) #{}) example)))
   body))

(defn- covered
  "Examples whose body is satisfied by the clause."
  [{:keys [body]} examples background]
  (filterv #(satisfies? body % background) examples))

(defn- uncovered
  "Examples whose body is NOT satisfied by the clause."
  [{:keys [body]} examples background]
  (filterv #(not (satisfies? body % background)) examples))

;;; ── Information gain ──────────────────────────────────────────────────────────

(defn- info-value
  "log₂(P/(P+N)) for the given clause. Returns 0.0 when P=0."
  [clause pos neg background]
  (let [p (count (covered clause pos background))]
    (if (zero? p)
      0.0
      (let [n (count (covered clause neg background))]
        (* (Math/log (/ (double p) (+ p n))) 1.442695)))))  ; × 1/ln2 → log₂

(defn- compute-gain
  "R × (new-info − base-info). Returns −1.0 when no positives are retained."
  [test-clause pos neg base-info background]
  (let [r (count (covered test-clause pos background))]
    (if (zero? r)
      -1.0
      (* r (- (info-value test-clause pos neg background) base-info)))))

;;; ── Clause construction ───────────────────────────────────────────────────────

(defn- make-clause [goal-kw]
  {:head {:op goal-kw :args ["X"]} :body []})

(defn- add-literal
  "Append a unary literal for pred-kw to the clause body.
   When positive? is false, wraps with NAF: {:op :not :args [inner]}."
  [clause pred-kw positive?]
  (let [lit {:op pred-kw :args ["X"]}]
    (update clause :body conj (if positive? lit {:op :not :args [lit]}))))

(defn- enumerate
  "Fallback: restrict clause to cover only the first positive example via
   a member literal. Guards against empty pos-examples."
  [clause pos-examples]
  (if (empty? pos-examples)
    clause
    (update clause :body conj {:op :member :args ["X" #{(first pos-examples)}]})))

;;; ── Best-literal selection ────────────────────────────────────────────────────

(defn- best-literal
  "Scan predicates for the one with the highest information gain when added
   to clause. Returns [best-pred-kw best-gain]; best-gain is −1.0 when
   no predicate improves coverage.
   background: current background (may include materialised exception preds)."
  [clause pos neg predicates background]
  (let [base-info (info-value clause pos neg background)]
    (reduce (fn [[best-kw best-ig] pred-kw]
              (let [candidate (add-literal clause pred-kw true)
                    gain      (compute-gain candidate pos neg base-info background)]
                (cond
                  (> gain best-ig)              [pred-kw gain]
                  ;; On tie, new literal wins unless current best has fewer body vars.
                  ;; Matches choose_tie_clause in fold.pl: last tie wins when var counts equal.
                  (and (>= gain 0.0) (= gain best-ig))
                  (let [cur-vars  (count (filter string? (mapcat :args (:body (add-literal clause best-kw true)))))
                        new-vars  (count (filter string? (mapcat :args (:body candidate))))]
                    (if (< cur-vars new-vars) [best-kw best-ig] [pred-kw gain]))
                  :else                         [best-kw best-ig])))
            [nil -1.0]
            predicates)))

;;; ── Materialisation ───────────────────────────────────────────────────────────

(defn- materialise
  "Evaluate rules against background and extend background with the head
   predicate's coverage. Used after learning exception rules so that
   subsequent (not ab_N(X)) evaluations resolve correctly.
   Argument order matches (update state :bg materialise rules all-examples)."
  [background rules all-examples]
  (reduce (fn [bg rule]
            (let [head-kw       (get-in rule [:head :op])
                  newly-covered (into #{} (filter #(satisfies? (:body rule) % bg) all-examples))]
              (update bg head-kw (fnil into #{}) newly-covered)))
          background
          rules))

;;; ── State helpers ─────────────────────────────────────────────────────────────
;;
;; State map: {:n-ab  int          — exception predicate counter (ab0, ab1, …)
;;             :ab    [rule …]     — accumulated exception rules (scasp-clj format)
;;             :bg    {pred #{…}}  — current background; extended as exceptions are learned}

(defn- make-state [background]
  {:n-ab 0 :ab [] :bg background})

;;; ── Mutual recursion: fold-loop ↔ specialize ↔ exception ─────────────────────

(declare fold-loop)

(defn- exception
  "Attempt to learn an exception predicate ab_N when the current clause
   still covers some negative examples.

   neg-as-pos: covered negatives — these become the exception's positive examples
   pos-as-neg: remaining positives — constrain the exception (do not over-generalise)

   On success:
     - Runs fold-loop to learn ab_N rules from neg-as-pos vs pos-as-neg.
     - Materialises the ab_N coverage into state :bg so NAF resolves correctly.
     - Returns [updated-clause state] with (not ab_N(X)) appended to the body.
   On failure (no distinguishing literal): returns [nil state]."
  [clause neg-as-pos pos-as-neg predicates state]
  (let [bg         (:bg state)
        [_ best-ig] (best-literal clause neg-as-pos pos-as-neg predicates bg)]
    (if (>= best-ig 0.0)
      (let [n-ab      (:n-ab state)
            ab-kw     (keyword (str "ab" n-ab))
            state1    (update state :n-ab inc)
            [ab-rules state2] (fold-loop ab-kw neg-as-pos pos-as-neg predicates state1)
            ;; Materialise ab_N rules into background so satisfies? can evaluate
            ;; (not ab_N(X)) in subsequent coverage checks.
            all-ex    (into #{} (concat neg-as-pos pos-as-neg))
            state3    (-> state2
                          (update :ab into ab-rules)
                          (update :bg materialise ab-rules all-ex))
            updated   (update clause :body conj {:op :not :args [{:op ab-kw :args ["X"]}]})]
        [updated state3])
      [nil state])))

(defn- specialize
  "Iteratively add literals to clause until no negative examples remain covered.

   Tries three strategies in order:
     1. Add the literal with the highest information gain (removes it from
        the candidate set so it cannot be reused in this clause chain).
     2. just-started? true  → enumerate: hardcode a specific positive example.
     3. just-started? false → exception: generate an ab_N predicate. Falls
        back to enumerate if no distinguishing literal exists.

   Returns [specialised-clause remaining-predicates state]."
  [clause pos neg predicates state just-started?]
  (let [bg (:bg state)
        [best-kw best-ig] (best-literal clause pos neg predicates bg)
        [new-clause new-preds state1]
        (cond
          (>= best-ig 0.0)
          [(add-literal clause best-kw true)
           (remove #{best-kw} predicates)
           state]

          just-started?
          [(enumerate clause pos) predicates state]

          :else
          (let [[exc-clause exc-state] (exception clause neg pos predicates state)]
            [(or exc-clause (enumerate clause pos)) predicates (or exc-state state)]))

        ;; Use updated :bg from state1 — may include newly materialised ab_N facts.
        bg1           (:bg state1)
        neg-remaining (covered new-clause neg bg1)]
    (if (empty? neg-remaining)
      [new-clause new-preds state1]
      (specialize new-clause
                  (uncovered new-clause pos bg1)
                  neg-remaining
                  new-preds state1 false))))

(defn- fold-loop
  "Iteratively specialise until all positive examples are covered.
   Passes the (potentially reduced) predicate set across iterations so that
   predicates used in earlier clauses are not reused in later ones.

   Returns [learned-rules state]."
  [goal-kw pos neg predicates state]
  (if (empty? pos)
    [[] state]
    (let [[clause remaining-preds state1]
          (specialize (make-clause goal-kw) pos neg predicates state true)
          bg1           (:bg state1)
          pos-remaining (uncovered clause pos bg1)
          [more-rules state2]
          (fold-loop goal-kw pos-remaining neg remaining-preds state1)]
      [(into [clause] more-rules) state2])))

;;; ── Public API ────────────────────────────────────────────────────────────────

(defn induce
  "Run the FOLD-R algorithm and return learned rules in scasp-clj format.

   Parameters
     goal-kw      — keyword for the target predicate, e.g. :liked
     pos-examples — seq of example keywords, e.g. [:b1 :b2]
     neg-examples — seq of negative example keywords (may be empty)
     background   — {pred-kw #{example-kw ...}} propositionalized ground facts
     predicates   — seq of pred-kws available for specialisation

   Returns
     {:positive-rules  [{:head term :body [term ...]} ...]
      :exception-rules [{:head term :body [term ...]} ...]}

   All rules are in scasp-clj format. Concatenate both seqs to get the full
   rule set for scasp.main/solve-all."
  [goal-kw pos-examples neg-examples background predicates]
  {:pre [(keyword? goal-kw)
         (every? keyword? pos-examples)
         (every? keyword? neg-examples)
         (map? background)]}
  (let [[pos-rules final-state]
        (fold-loop goal-kw
                   (vec pos-examples)
                   (vec neg-examples)
                   (vec predicates)
                   (make-state background))]
    {:positive-rules  pos-rules
     :exception-rules (:ab final-state)}))

;;; ── Propositionalization helper ───────────────────────────────────────────────

(defn propositionalize
  "Convert a seq of scasp-clj ground facts (rules with empty :body) into the
   {pred-kw #{example-kw}} background map required by induce.

   Unary  {:head {:op :bean  :args [:b1]}      :body []} → {:bean #{:b1}}
   Binary {:head {:op :from  :args [:b1 :s1]}  :body []} → {:from_s1 #{:b1}}
   Arity ≥ 3 facts are dropped.

   Also accepts bare term maps {:op :pred :args [...]} without a :head wrapper."
  [facts]
  (reduce
   (fn [bg fact]
     (let [term (if (contains? fact :head) (:head fact) fact)
           op   (:op term)
           args (:args term)]
       ;; Skip terms with variable args (strings) — they are type hints, not ground facts.
       (if (some string? args)
         bg
         (case (count args)
           1 (update bg op (fnil conj #{}) (first args))
           2 (let [prop-kw (keyword (str (name op) "_" (name (second args))))]
               (update bg prop-kw (fnil conj #{}) (first args)))
           bg))))
   {}
   facts))
