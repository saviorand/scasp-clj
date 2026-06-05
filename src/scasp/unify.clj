(ns scasp.unify
  "Unification engine for s(CASP).

   solve-unify : t1 t2 ve → ve | nil   (nil = failure)
   solve-dnunify : t1 t2 ve → ve | nil  (disequality)
   occurs-check : var t ve → bool       (true = ok, false = cycle)"
  (:require [scasp.term :as term]
            [scasp.vars :as vars]))

;;; ── Occurs check ─────────────────────────────────────────────────────────────

(defn occurs-check
  "Return false if var-name occurs in term t (would create a cycle), else true."
  [var-name t ve]
  (cond
    (term/is-var? t)
    (let [id1 (vars/get-value-id var-name ve)
          id2 (vars/get-value-id t ve)]
      (cond
        (and id1 id2 (= id1 id2)) false ; same ID → cycle
        :else
        (let [v (vars/var-value t ve)]
          (if (contains? v :val)
            (recur var-name (:val v) ve)
            true)))) ; unbound → no cycle
    (term/is-compound? t)
    (every? #(occurs-check var-name % ve) (:args t))
    :else true))

;;; ── is-atom helpers (resolve variable to atom or return as-is) ───────────────

(defn- atom-value
  "If t is an atom/number directly, return it.
   If t is a bound variable, return its bound value if atom/number.
   Otherwise nil."
  [t ve]
  (cond
    (or (term/is-atom? t) (term/is-number? t)) t
    (term/is-var? t)
    (let [v (vars/var-value t ve)]
      (when (contains? v :val)
        (let [val (:val v)]
          (when (or (term/is-atom? val) (term/is-number? val)) val))))
    :else nil))

(defn- compound-value
  "Resolve t to a compound, following variable bindings.
   Returns [compound resolved-ve] or nil."
  [t ve]
  (cond
    (term/is-compound? t) [t ve]
    (term/is-var? t)
    (let [v (vars/var-value t ve)]
      (when (contains? v :val)
        (let [val (:val v)]
          (when (term/is-compound? val) [val ve]))))
    :else nil))

;;; ── Main unification ─────────────────────────────────────────────────────────

(declare solve-unify)

(defn solve-subunify
  "Unify two argument lists element-wise. Returns updated ve or nil."
  [args1 args2 ve oc?]
  (cond
    (and (empty? args1) (empty? args2)) ve
    (or (empty? args1) (empty? args2)) nil
    :else
    (when-let [ve' (solve-unify (first args1) (first args2) ve oc?)]
      (recur (rest args1) (rest args2) ve' oc?))))

(defn solve-unify
  "Unify t1 and t2 in var-env ve.
   oc? – perform occurs check if true.
   Returns updated ve on success, nil on failure."
  [t1 t2 ve oc?]
  (cond
    ;; var – var
    (and (term/is-var? t1) (term/is-var? t2))
    (vars/unify-vars t1 t2 ve)

    ;; atom/number – atom/number
    (and (atom-value t1 ve) (atom-value t2 ve))
    (when (= (atom-value t1 ve) (atom-value t2 ve)) ve)

    ;; compound – compound (same functor & arity)
    (let [[c1 _] (compound-value t1 ve)
          [c2 _] (compound-value t2 ve)]
      (and c1 c2
           (= (:op c1) (:op c2))
           (= (count (:args c1)) (count (:args c2)))))
    (let [[c1 _] (compound-value t1 ve)
          [c2 _] (compound-value t2 ve)]
      (solve-subunify (:args c1) (:args c2) ve oc?))

    ;; var – non-var (bind variable)
    (term/is-var? t1)
    (when-let [cs (vars/is-unbound? t1 ve)]
      (when (:bindable? cs)
        (let [t2r (vars/resolve-term t2 ve)]
          (when (or (not oc?) (occurs-check t1 t2r ve))
            (when-let [ve' (vars/test-constraints (:constraints cs) t2r ve)]
              (if (number? t2r)
                (when (and (vars/check-numeric-bounds (:numeric-bounds cs) t2r)
                           (not (contains? (:numeric-neq cs) t2r)))
                  (vars/update-var-value t1 {:val t2r} ve'))
                (vars/update-var-value t1 {:val t2r} ve')))))))

    ;; non-var – var (symmetric)
    (term/is-var? t2)
    (solve-unify t2 t1 ve oc?)

    :else nil))

;;; ── Disequality ──────────────────────────────────────────────────────────────

(declare solve-dnunify)

(defn solve-subdnunify
  "Disequality for two arg lists.  Returns [ve flag] where flag is :constraint or :ground."
  [args1 args2 ve]
  (when (and (seq args1) (seq args2))
    (let [a1 (first args1) a2 (first args2)]
      (let [r (solve-dnunify a1 a2 ve)]
        ;; If first pair produced a constraint (unbound var got constrained), keep going
        (if r
          [r :constraint]
          ;; first pair fails to dnunify → they must unify. Try rest.
          (when-let [ve' (solve-unify a1 a2 ve false)]
            (let [result (solve-subdnunify (rest args1) (rest args2) ve')]
              result)))))))

(defn solve-dnunify
  "Add a disequality constraint between t1 and t2.
   Returns updated ve or nil on failure (they must be equal)."
  [t1 t2 ve]
  (let [t1r (vars/resolve-term t1 ve)
        t2r (vars/resolve-term t2 ve)]
    (cond
      ;; Both unbound variables → error (at least one must be ground)
      (and (term/is-var? t1r) (vars/is-unbound? t1r ve)
           (term/is-var? t2r) (vars/is-unbound? t2r ve))
      (throw (ex-info "Disequality requires at least one ground argument"
                      {:t1 t1 :t2 t2}))

      ;; t1 is unbound → add constraint t2r to t1
      (and (term/is-var? t1r) (vars/is-unbound? t1r ve))
      (if (vars/is-ground? t2r ve)
        (vars/add-var-constraint t1r t2r ve)
        (throw (ex-info "Disequality requires at least one ground argument"
                        {:t1 t1r :t2 t2r})))

      ;; t2 is unbound → add constraint t1r to t2
      (and (term/is-var? t2r) (vars/is-unbound? t2r ve))
      (if (vars/is-ground? t1r ve)
        (vars/add-var-constraint t2r t1r ve)
        (throw (ex-info "Disequality requires at least one ground argument"
                        {:t1 t1r :t2 t2r})))

      ;; Both atoms / numbers
      (and (atom-value t1r ve) (atom-value t2r ve))
      (when (not= (atom-value t1r ve) (atom-value t2r ve)) ve)

      ;; Both compounds: same functor → must differ in at least one arg
      (let [[c1 _] (compound-value t1r ve)
            [c2 _] (compound-value t2r ve)]
        (and c1 c2
             (= (:op c1) (:op c2))
             (= (count (:args c1)) (count (:args c2)))))
      (let [[c1 _] (compound-value t1r ve)
            [c2 _] (compound-value t2r ve)
            result (solve-subdnunify (:args c1) (:args c2) ve)]
        (when result (first result)))

      ;; Different types / different functor/arity → automatically succeed
      :else ve)))
