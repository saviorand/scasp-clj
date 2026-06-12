(ns scasp.chs
  "Coinductive Hypothesis Set (CHS).

   The CHS tracks which goals are on the current proof path, preventing
   infinite loops and enabling coinductive success/failure.

   CHS structure:
     {functor-str → [{:args [term…] :success? bool :nmr? bool} …]}

   check-chs returns a lazy sequence of result maps:
     {:result  :not-present | :coinductive-success
      :var-env <updated>
      :even-loop {:cycle [goal…] :cvars [var…]} | nil}

   nil result in the seq means failure (constructive coinductive failure applied)."
  (:require [scasp.term   :as term]
            [scasp.vars   :as vars]
            [scasp.unify  :as unify]))

;;; ── Construction ─────────────────────────────────────────────────────────────

(defn new-chs [] {})

;;; ── Entry helpers ────────────────────────────────────────────────────────────

(defn- make-entry [args success? nmr?]
  {:args (vec args) :success? success? :nmr? nmr?})

(defn- entries-for [functor chs]
  (get chs functor []))

;;; ── Exact match ──────────────────────────────────────────────────────────────

(defn- exact-match-args?
  "Strict check: unbound var only matches unbound var with same constraints."
  [a1 a2 ve]
  (cond
    (= a1 a2) true

    (and (term/is-var? a1) (term/is-var? a2))
    (let [v1 (vars/var-value a1 ve)
          v2 (vars/var-value a2 ve)]
      (cond
        (and (contains? v1 :val) (contains? v2 :val))
        (exact-match-args? (:val v1) (:val v2) ve)

        (and (not (contains? v1 :val)) (not (contains? v2 :val)))
        (= (:constraints v1) (:constraints v2))

        :else false))

    (term/is-var? a1)
    (let [v1 (vars/var-value a1 ve)]
      (when (contains? v1 :val)
        (exact-match-args? (:val v1) a2 ve)))

    (term/is-var? a2)
    (let [v2 (vars/var-value a2 ve)]
      (when (contains? v2 :val)
        (exact-match-args? a1 (:val v2) ve)))

    (and (term/is-compound? a1) (term/is-compound? a2)
         (= (:op a1) (:op a2))
         (= (count (:args a1)) (count (:args a2))))
    (every? true? (map #(exact-match-args? %1 %2 ve) (:args a1) (:args a2)))

    :else false))

(defn exact-match
  "Find the first entry in entries whose args exactly match args under ve.
   Returns the entry or nil."
  [args entries ve]
  (some (fn [e]
          (when (and (= (count (:args e)) (count args))
                     (every? true? (map #(exact-match-args? %1 %2 ve) args (:args e))))
            e))
        entries))

;;; ── Add / remove entries ─────────────────────────────────────────────────────

(defn add-to-chs
  "Add an entry for functor with args. Returns [entry updated-chs updated-ve].
   even-loop-cvars is a collection of variable names that are loop variables
   (from prior even-loops on this branch); their args are kept live while other
   unbound vars are frozen (bindable? false) before storage."
  ([functor args success? nmr? chs ve]
   (add-to-chs functor args success? nmr? chs ve []))
  ([functor args success? nmr? chs ve even-loop-cvars]
   (let [[frozen-args ve'] (vars/replace-args-for-chs args even-loop-cvars ve)
         e                 (make-entry frozen-args success? nmr?)
         chs'              (update chs functor (fnil conj []) e)]
     [e chs' ve'])))

(defn remove-from-chs
  "Remove a specific entry (by identity) from the CHS.
   Entries are added/removed in LIFO (DFS) order, so the target is almost always
   the last element — pop it in O(1); fall back to a linear rebuild otherwise."
  [entry functor chs]
  (update chs functor
          (fn [es]
            (cond
              (empty? es)               es
              (identical? (peek es) entry) (pop es)
              :else (vec (remove #(identical? % entry) es))))))

;;; ── Dual CHS helpers ─────────────────────────────────────────────────────────

(defn- coinductive-failure?
  "True if there is an exact-match CHS entry for the dual of functor/args
   that is still in-progress (success? false).  When the dual is in-progress,
   we know it will fail, so the current call coinductively succeeds."
  [functor args ve chs]
  (let [neg-f (term/negate-functor functor)]
    (boolean (exact-match args (filter (complement :success?) (entries-for neg-f chs)) ve))))

(defn- propagate-neg-constraints
  "Propagate disequality constraints from the in-progress dual entry's args
   onto the corresponding current-call args.  Returns updated ve."
  [functor args ve chs]
  (let [neg-f   (term/negate-functor functor)
        entries (filter (complement :success?) (entries-for neg-f chs))
        matched (exact-match args entries ve)]
    (if matched
      (reduce (fn [ve' [call-arg entry-arg]]
                (let [ev (vars/var-value entry-arg ve')]
                  (if (and (term/is-var? entry-arg)
                           (not (contains? ev :val))
                           (seq (:constraints ev)))
                    (reduce (fn [ve'' c]
                              (let [target (if (term/is-var? call-arg) call-arg entry-arg)]
                                (or (vars/add-var-constraint target c ve'')
                                    ve'')))
                            ve'
                            (:constraints ev))
                    ve')))
              ve
              (map vector args (:args matched)))
      ve)))

(defn- dual-entries-for-args
  "Return all CHS entries for the dual of functor whose args unify (but do not
   exactly match) with args.  Used for constructive coinductive failure."
  [functor args ve chs]
  (let [neg-f       (term/negate-functor functor)
        pos-entries (entries-for functor chs)
        neg-entries (entries-for neg-f chs)]
    ;; Only proceed if there is no exact match of the positive in the CHS
    (when-not (exact-match args (filter :success? pos-entries) ve)
      (filter (fn [e]
                (unify/solve-unify
                 (term/make-compound (term/functor-name-str functor) args)
                 (term/make-compound (term/functor-name-str functor) (:args e))
                 ve false))
              neg-entries))))

(defn- propagate-dual-constraints
  "Propagate disequality constraints from unifying (non-exact) dual-entry args
   onto the corresponding current-call args.  Returns updated ve."
  [args dual-entries ve]
  (reduce (fn [ve-acc entry]
            (reduce (fn [ve' [call-arg entry-arg]]
                      (let [ev (vars/var-value entry-arg ve')]
                        (if (and (term/is-var? entry-arg)
                                 (not (contains? ev :val))
                                 (seq (:constraints ev)))
                          (reduce (fn [ve'' c]
                                    (let [target (if (term/is-var? call-arg) call-arg entry-arg)]
                                      (or (vars/add-var-constraint target c ve'')
                                          ve'')))
                                  ve'
                                  (:constraints ev))
                          ve')))
                    ve-acc
                    (map vector args (:args entry))))
          ve
          dual-entries))

;;; ── Check call stack for loops ───────────────────────────────────────────────

(defn check-negations
  "Walk call-stack looking for an ancestor call with the same functor.
   call-stack entries are {:goal compound :rule any}.
   Returns {:result :positive-loop | :even-loop | :not-found
             :cycle  [goals from stack]
             :cvars  [variables non-ground in both calls]
             :var-env <updated>}."
  [functor args ve call-stack]
  (loop [[entry & rest-stack] call-stack
         neg-seen? false
         cycle     []]
    (if (nil? entry)
      {:result :not-found :cycle [] :cvars [] :var-env ve}
      (let [g   (:goal entry)
            gf  (when (term/is-compound? g) (term/term-functor g))]
        (cond
          ;; Intervening negation (dual call on stack)
          (and gf (term/is-dual? gf) (not= gf functor))
          (recur rest-stack true (conj cycle g))

          ;; Match found: same functor
          (and gf (= gf functor))
          (let [g-args (:args g)
                ve'    (unify/solve-unify
                        (term/make-compound (term/functor-name-str functor) args)
                        (term/make-compound (term/functor-name-str functor) g-args)
                        ve false)]
            (if ve'
              (if neg-seen?
                ;; Even loop: coinductive success with variable substitution info
                {:result :even-loop
                 :cycle  (conj cycle g)
                 :cvars  (vars/variable-intersection
                          (term/make-compound (term/functor-name-str functor) args)
                          g ve)
                 :var-env ve'}
                ;; Positive loop: fail
                {:result :positive-loop
                 :cycle  []
                 :cvars  []
                 :var-env ve})
              ;; Doesn't unify → keep going
              (recur rest-stack neg-seen? (conj cycle g))))

          :else
          (recur rest-stack neg-seen? (conj cycle g)))))))

;;; ── Main CHS check ───────────────────────────────────────────────────────────


(defn check-chs
  "Check the CHS for functor/args.  Structure mirrors check_chs/8 in chs.pl:

   Call-stack loop detection runs first:
   - Positive loop  → hard failure.
   - Even loop      → coinductive success (with loop info).

   Then CHS entry checks:
   1. Exact match of the *positive* with success=true → coinductive success.
   2. Exact match of the *dual* with success=false (in-progress) → coinductive
      success (the dual is about to fail, so the positive succeeds).
   3. Dual entries that unify but don't exactly match → propagate their
      constraints, then continue as :not-present.
   4. Otherwise → :not-present.

   Returns a lazy seq of result maps:
     {:result  :not-present | :coinductive-success
      :var-env <updated>
      :even-loop {:cycle [] :cvars []} | nil}
   Empty seq means failure."
  [functor args ve chs call-stack]
  (let [{:keys [result cycle cvars var-env]} (check-negations functor args ve call-stack)]
    (case result
      :positive-loop []

      :even-loop
      [{:result    :coinductive-success
        :var-env   var-env
        :even-loop {:cycle cycle :cvars cvars}}]

      ;; not-found in call stack: check CHS entries
      (let [entries (entries-for functor chs)]
        (cond
          ;; Coinductive success: completed positive entry matches
          (exact-match args (filter :success? entries) ve)
          [{:result :coinductive-success :var-env ve :even-loop {:cycle [] :cvars []}}]

          ;; Coinductive success via dual: dual is in-progress (will fail) → positive succeeds
          (coinductive-failure? functor args ve chs)
          [{:result    :coinductive-success
            :var-env   (propagate-neg-constraints functor args ve chs)
            :even-loop {:cycle [] :cvars []}}]

          ;; Constructive coinductive failure: dual entries unify → propagate + proceed
          :else
          (let [duals (dual-entries-for-args functor args ve chs)]
            [{:result    :not-present
              :var-env   (if (seq duals)
                           (propagate-dual-constraints args duals ve)
                           ve)
              :even-loop nil}]))))))
