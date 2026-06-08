(ns scasp.vars
  "Variable environment: explicit union-find structure for s(CASP) variable management.

   var-env structure:
     {:names  {var-name → initial-id}    ; string → int
      :values {id       → var-value}      ; int    → map
      :name-cnt int                       ; counter for fresh variable names
      :id-cnt   int}                      ; counter for fresh value IDs

   var-value is one of:
     {:val v}                                             ; bound to value v
     {:constraints    #{v1 …}                            ; unbound/constrained
      :numeric-bounds {:lo -Inf :hi +Inf :lo-open? bool :hi-open? bool}
      :numeric-neq    #{n…}
      :var-constraints [{:op kw :rhs var-name} …]        ; relational constraints vs other vars
      :bindable? bool :loop-var n}
     {:link id}                                           ; alias (union-find link)"
  (:require [scasp.term :as term]
            [clojure.set :as set]))

;;; ── Construction ─────────────────────────────────────────────────────────────

(defn new-var-env []
  {:names {} :values {} :name-cnt 0 :id-cnt 0})

;;; ── ID resolution (union-find) ───────────────────────────────────────────────

(defn get-final-id
  "Follow :link chains starting from id; return the terminal (non-link) id."
  [id ve]
  (if-let [v (get (:values ve) id)]
    (if-let [link (:link v)]
      (recur link ve)
      id)
    id))

(defn get-value-id
  "Return the final value-id for var-name, or nil if not in env."
  [var-name ve]
  (when-let [init (get (:names ve) var-name)]
    (get-final-id init ve)))

(defn get-value-by-id
  "Return the value struct for a final id (must be non-link)."
  [id ve]
  (get (:values ve) id))

;;; ── Variable value lookup ────────────────────────────────────────────────────

;;; ── Numeric bounds helpers ───────────────────────────────────────────────────

(def ^:private +inf #?(:clj Double/POSITIVE_INFINITY :cljs js/Infinity))
(def ^:private -inf #?(:clj Double/NEGATIVE_INFINITY :cljs (- js/Infinity)))

(def empty-numeric-bounds
  {:lo -inf :hi +inf :lo-open? true :hi-open? true})

(defn- bounds-consistent?
  "Return true if the interval [lo, hi] (with open/closed flags) is non-empty."
  [{:keys [lo hi lo-open? hi-open?]}]
  (cond
    (> lo hi) false
    (= lo hi) (and (not lo-open?) (not hi-open?))
    :else true))

(defn tighten-lo
  "Return updated bounds with lo raised to v (strict if open?), or nil if inconsistent."
  [{:keys [lo lo-open?] :as bounds} v open?]
  (let [new-lo   (if (> v lo) v lo)
        new-open (if (> v lo) open?
                   (if (= v lo) (or lo-open? open?) lo-open?))
        b' (assoc bounds :lo new-lo :lo-open? new-open)]
    (when (bounds-consistent? b') b')))

(defn tighten-hi
  "Return updated bounds with hi lowered to v (strict if open?), or nil if inconsistent."
  [{:keys [hi hi-open?] :as bounds} v open?]
  (let [new-hi   (if (< v hi) v hi)
        new-open (if (< v hi) open?
                   (if (= v hi) (or hi-open? open?) hi-open?))
        b' (assoc bounds :hi new-hi :hi-open? new-open)]
    (when (bounds-consistent? b') b')))

(defn merge-numeric-bounds
  "Intersect two numeric-bounds maps.  Returns merged bounds or nil if empty."
  [b1 b2]
  (-> b1
      (tighten-lo (:lo b2) (:lo-open? b2))
      (some-> (tighten-hi (:hi b2) (:hi-open? b2)))))

(defn check-numeric-bounds
  "Return true if numeric value v satisfies bounds."
  [{:keys [lo hi lo-open? hi-open?] :as _bounds} v]
  (and (if lo-open? (> v lo) (>= v lo))
       (if hi-open? (< v hi) (<= v hi))))

(def ^:private default-unbound
  {:constraints #{} :numeric-bounds empty-numeric-bounds :numeric-neq #{} :var-constraints [] :bindable? true :loop-var 0})

(defn var-value
  "Return the value struct for var-name.
   If not in env returns the default unbound struct."
  [var-name ve]
  (if-let [id (get-value-id var-name ve)]
    (get-value-by-id id ve)
    default-unbound))

(defn is-unbound?
  "Return the constraint struct if var-name is unbound/constrained; nil if bound."
  [var-name ve]
  (let [v (var-value var-name ve)]
    (when-not (contains? v :val) v)))

(defn is-ground?
  "True if term contains no unbound variables."
  [t ve]
  (cond
    (term/is-var? t)
    (let [v (var-value t ve)]
      (if (contains? v :val)
        (recur (:val v) ve)
        false))
    (term/is-compound? t)
    (every? #(is-ground? % ve) (:args t))
    :else true))

;;; ── Value updates ────────────────────────────────────────────────────────────

(defn update-var-value
  "Set the value struct for var-name.
   If the variable already has an ID, updates the terminal id's slot.
   If not in env, creates a new ID and name entry."
  [var-name val ve]
  (if-let [id (get-value-id var-name ve)]
    (assoc-in ve [:values id] val)
    (let [id (:id-cnt ve)]
      (-> ve
          (assoc-in [:names var-name] id)
          (assoc-in [:values id] val)
          (update :id-cnt inc)))))

;;; ── Constraint management ────────────────────────────────────────────────────

(defn test-constraints
  "Check that ground value val does not violate any disequality or numeric constraints.
   Returns ve unchanged on success, nil on violation."
  [constraints val ve]
  (cond
    (contains? constraints val) nil
    :else ve))

(defn test-numeric-constraints
  "Check val against numeric-bounds and numeric-neq.  Returns ve or nil."
  [numeric-bounds numeric-neq val ve]
  (when (number? val)
    (when (check-numeric-bounds numeric-bounds val)
      (when-not (contains? numeric-neq val)
        ve))))

(defn add-var-constraint
  "Add forbidden value c to var-name's constraint set.
   Returns updated ve or nil if variable is already bound."
  [var-name c ve]
  (when-let [cs (is-unbound? var-name ve)]
    (let [new-cs (update cs :constraints conj c)]
      (update-var-value var-name new-cs ve))))

(defn add-numeric-bound
  "Add a numeric inequality constraint on var-name.
   op is one of :< :> :=< :>= :=:= :arith-ne, val is the ground numeric value.
   Returns updated ve or nil on immediate inconsistency."
  [var-name op val ve]
  (when-let [cs (is-unbound? var-name ve)]
    (let [bounds (:numeric-bounds cs)
          neq    (:numeric-neq cs)]
      (case op
        :>    (when-let [b' (tighten-lo bounds val true)]
                (update-var-value var-name (assoc cs :numeric-bounds b') ve))
        :>=   (when-let [b' (tighten-lo bounds val false)]
                (update-var-value var-name (assoc cs :numeric-bounds b') ve))
        :<    (when-let [b' (tighten-hi bounds val true)]
                (update-var-value var-name (assoc cs :numeric-bounds b') ve))
        :=<   (when-let [b' (tighten-hi bounds val false)]
                (update-var-value var-name (assoc cs :numeric-bounds b') ve))
        :=:=  (when (check-numeric-bounds bounds val)
                (when-not (contains? neq val)
                  (update-var-value var-name {:val val} ve)))
        :arith-ne (let [new-neq (conj neq val)]
                    (if (and (not (= (:lo bounds) (:hi bounds)))
                             (= (:lo bounds) val) (= (:hi bounds) val))
                      nil  ; single-point interval and we're excluding that point
                      (update-var-value var-name (assoc cs :numeric-neq new-neq) ve)))
        nil))))

(defn add-var-relational-constraint
  "Record a constraint lhs-var op rhs-var where both are currently unbound.
   op is the canonical bound-op keyword (:< :> :=< :>= :=:= :arith-ne).
   Returns updated ve."
  [lhs-var op rhs-var ve]
  (if-let [cs (is-unbound? lhs-var ve)]
    (update-var-value lhs-var
                      (update cs :var-constraints (fnil conj []) {:op op :rhs rhs-var})
                      ve)
    ve))

(defn- flip-op [op]
  (case op
    :<       :>
    :>       :<
    :=<      :>=
    :>=      :=<
    :=:=     :=:=
    :arith-ne :arith-ne
    nil))

(defn- coerce-int
  "Return n as an integer if it is a whole number, otherwise return it unchanged."
  [n]
  #?(:clj  (if (and (float? n) (== n (Math/floor n))) (long n) n)
     :cljs (if (and (not (integer? n)) (== n (js/Math.floor n))) (int n) n)))

(defn- unify-or-bind
  "Unify var-name with ground value val.  Returns ve or nil."
  [var-name val ve]
  (let [v   (var-value var-name ve)
        val (if (number? val) (coerce-int val) val)]
    (if (contains? v :val)
      (when (== (:val v) val) ve)
      (when (:bindable? v)
        (update-var-value var-name {:val val} ve)))))

(defn check-var-constraints
  "When var-name is being bound to numeric val, check all var-constraints.
   Handles both relational (:< :> etc.) and :linear-eq constraints.
   Returns updated ve on success, nil on violation."
  [var-name val ve]
  (if-let [cs (is-unbound? var-name ve)]
    (reduce (fn [ve' {:keys [op rhs] :as c}]
              (when ve'
                (if (= op :linear-eq)
                  ;; X is being bound to val; constraint says X = coeff*rhs + offset
                  ;; → derive rhs = (val - offset) / coeff and bind/check it
                  (let [{:keys [coeff offset]} c
                        rhs-v (var-value rhs ve')]
                    (if (contains? rhs-v :val)
                      (when (== val (+ (* coeff (:val rhs-v)) offset)) ve')
                      (when-not (zero? coeff)
                        (unify-or-bind rhs (/ (- val offset) coeff) ve'))))
                  ;; Relational constraint
                  (let [rhs-v (var-value rhs ve')]
                    (if (contains? rhs-v :val)
                      (let [rv (:val rhs-v)]
                        (when (number? rv)
                          (case op
                            :<       (when (<  val rv) ve')
                            :>       (when (>  val rv) ve')
                            :=<      (when (<= val rv) ve')
                            :>=      (when (>= val rv) ve')
                            :=:=     (when (== val rv) ve')
                            :arith-ne (when (not (== val rv)) ve')
                            ve')))
                      (if-let [flipped (flip-op op)]
                        (add-numeric-bound rhs flipped val ve')
                        ve'))))))
            ve
            (:var-constraints cs))
    ve))

;;; ── Linear equality constraints (X is coeff*Y + offset) ─────────────────────

(defn add-linear-eq
  "Record X = coeff * Y + offset, where X and/or Y may be unbound.
   - If both are ground numbers, check the equality and return ve or nil.
   - If X is bound to a number xv, derive Y = (xv - offset) / coeff and unify.
   - If Y is bound to a number yv, derive X = coeff*yv + offset and unify.
   - If both are unbound, store {:op :linear-eq :coeff coeff :rhs Y :offset offset}
     on X, and the inverse {:op :linear-eq :coeff (1/coeff) :rhs X :offset (-offset/coeff)}
     on Y so that binding either one later triggers propagation."
  [x-term coeff y-var offset ve]
  (let [xv (when (term/is-var? x-term)
              (let [v (var-value x-term ve)]
                (when (contains? v :val) (:val v))))
        x-num (when (number? x-term) x-term)
        x-val (or xv x-num)
        yv    (let [v (var-value y-var ve)]
                (when (contains? v :val) (:val v)))]
    (cond
      ;; Both ground — check equality
      (and x-val yv)
      (when (== x-val (+ (* coeff yv) offset)) ve)

      ;; X is ground — derive Y
      x-val
      (when-not (zero? coeff)
        (let [y-derived (/ (- x-val offset) coeff)]
          (unify-or-bind y-var y-derived ve)))

      ;; Y is ground — derive X
      yv
      (let [x-derived (+ (* coeff yv) offset)]
        (if (term/is-var? x-term)
          (unify-or-bind x-term x-derived ve)
          (when (== x-term x-derived) ve)))

      ;; Both unbound — store deferred constraints
      (and (term/is-var? x-term) (is-unbound? x-term ve) (is-unbound? y-var ve))
      (let [ve' (if-let [cs (is-unbound? x-term ve)]
                  (update-var-value x-term
                                    (update cs :var-constraints (fnil conj [])
                                            {:op :linear-eq :coeff coeff :rhs y-var :offset offset})
                                    ve)
                  ve)]
        (if-let [cs (is-unbound? y-var ve')]
          (let [inv-coeff (if (zero? coeff) nil (/ 1.0 coeff))
                inv-offset (if (zero? coeff) nil (/ (- offset) coeff))]
            (if inv-coeff
              (update-var-value y-var
                                (update cs :var-constraints (fnil conj [])
                                        {:op :linear-eq :coeff inv-coeff :rhs (if (term/is-var? x-term) x-term x-term) :offset inv-offset})
                                ve')
              ve'))
          ve'))

      :else ve)))

;;; ── Union-find: unify two variables ─────────────────────────────────────────

(defn- merge-loop-var [lv1 lv2]
  (if (or (= lv1 -1) (= lv2 -1)) -1 (max lv1 lv2)))

(defn unify-vars
  "Unify two variables in var-env using union-find.
   Returns updated ve or nil on failure."
  [v1 v2 ve]
  (let [id1 (get-value-id v1 ve)
        id2 (get-value-id v2 ve)]
    (cond
      ;; Already share the same terminal ID → no-op
      (and id1 id2 (= id1 id2))
      ve

      ;; Both unbound/constrained → merge into v1, link v2 → v1
      (and (is-unbound? v1 ve) (is-unbound? v2 ve))
      (let [u1  (is-unbound? v1 ve)
            u2  (is-unbound? v2 ve)
            merged-bounds (merge-numeric-bounds (:numeric-bounds u1) (:numeric-bounds u2))]
        (when merged-bounds
          (let [merged {:constraints    (set/union (:constraints u1) (:constraints u2))
                        :numeric-bounds merged-bounds
                        :numeric-neq    (set/union (:numeric-neq u1) (:numeric-neq u2))
                        :var-constraints (into (vec (:var-constraints u1)) (:var-constraints u2))
                        :bindable?      (and (:bindable? u1) (:bindable? u2))
                        :loop-var       (merge-loop-var (:loop-var u1) (:loop-var u2))}
                ve1 (update-var-value v1 merged ve)
                fid (get-value-id v1 ve1)]
            (if id2
              (assoc-in ve1 [:values id2] {:link fid})
              (let [new-id (:id-cnt ve1)]
                (-> ve1
                    (assoc-in [:names v2] new-id)
                    (assoc-in [:values new-id] {:link fid})
                    (update :id-cnt inc)))))))

      ;; v1 unbound, v2 bound → link v1 → v2
      (is-unbound? v1 ve)
      (let [{:keys [constraints numeric-bounds numeric-neq bindable?]} (is-unbound? v1 ve)]
        (when bindable?
          (let [val (:val (var-value v2 ve))]
            (when-let [ve' (test-constraints constraints val ve)]
              (when (or (not (number? val))
                        (and (check-numeric-bounds numeric-bounds val)
                             (not (contains? numeric-neq val))))
                (when-let [ve'' (if (number? val)
                                  (check-var-constraints v1 val ve')
                                  ve')]
                  (let [fid2 (or id2 (get-value-id v2 ve''))]
                    (if fid2
                      (if id1
                        (assoc-in ve'' [:values id1] {:link fid2})
                        (let [new-id (:id-cnt ve'')]
                          (-> ve''
                              (assoc-in [:names v1] new-id)
                              (assoc-in [:values new-id] {:link fid2})
                              (update :id-cnt inc))))
                      ;; v2 was never in env; just bind v1 directly
                      (update-var-value v1 {:val val} ve'')))))))))

      ;; v2 unbound, v1 bound → link v2 → v1
      (is-unbound? v2 ve)
      (let [{:keys [constraints numeric-bounds numeric-neq bindable?]} (is-unbound? v2 ve)]
        (when bindable?
          (let [val (:val (var-value v1 ve))]
            (when-let [ve' (test-constraints constraints val ve)]
              (when (or (not (number? val))
                        (and (check-numeric-bounds numeric-bounds val)
                             (not (contains? numeric-neq val))))
                (when-let [ve'' (if (number? val)
                                  (check-var-constraints v2 val ve')
                                  ve')]
                  (if id1
                    (if id2
                      (assoc-in ve'' [:values id2] {:link id1})
                      (let [new-id (:id-cnt ve'')]
                        (-> ve''
                            (assoc-in [:names v2] new-id)
                            (assoc-in [:values new-id] {:link id1})
                            (update :id-cnt inc))))
                    (update-var-value v2 {:val val} ve''))))))))

      :else nil)))

;;; ── Fresh variable generation ────────────────────────────────────────────────

(defn generate-unique-var
  "Create a fresh variable name using prefix and the current name counter.
   Returns [new-var-name updated-ve]."
  ([ve] (generate-unique-var "_G" ve))
  ([prefix ve]
   (let [n   (:name-cnt ve)
         nm  (str "_" prefix n)]
     [nm (update ve :name-cnt inc)])))

;;; ── Alpha-renaming for rule expansion ────────────────────────────────────────

(defn get-unique-vars
  "Rename all variables in head and body to fresh unique names.
   Returns [renamed-head renamed-body updated-ve]."
  [head body ve]
  (let [all-vars (set/union (term/term-vars head) (term/terms-vars body))
        [rename-map ve']
        (reduce (fn [[m ve] v]
                  (let [[fresh ve'] (generate-unique-var v ve)]
                    [(assoc m v fresh) ve']))
                [{} ve]
                all-vars)
        rename (fn [t] (reduce-kv (fn [acc k v] (term/substitute k v acc)) t rename-map))
        new-head (rename head)
        new-body (mapv rename body)]
    [new-head new-body ve']))

;;; ── Variable intersection (for even-loop detection) ─────────────────────────

(defn variable-intersection
  "Variables that are non-ground in both t1 and t2."
  [t1 t2 ve]
  (let [v1 (into #{} (filter #(is-unbound? % ve)) (term/term-vars t1))
        v2 (into #{} (filter #(is-unbound? % ve)) (term/term-vars t2))
        ;; intersect by value-id
        ids1 (into #{} (keep #(get-value-id % ve)) v1)
        ids2 (into #{} (keep #(get-value-id % ve)) v2)
        shared (set/intersection ids1 ids2)]
    (into [] (filter (fn [v] (contains? shared (get-value-id v ve)))) v1)))

;;; ── Even-loop variable substitution ─────────────────────────────────────────

(defn replace-vars-for-chs
  "Walk term t, replacing variables for CHS storage.
   Loop vars (in loop-var-ids set of value-ids) are kept as-is.
   Other unbound vars are replaced with a fresh frozen var (bindable? false).
   Bound vars are substituted with their value.
   Returns [term' updated-ve mapping] where mapping is {old-name → new-name}."
  ([t loop-var-ids ve]
   (replace-vars-for-chs t loop-var-ids ve {}))
  ([t loop-var-ids ve mapping]
   (cond
     (term/is-var? t)
     (let [v (var-value t ve)]
       (cond
         ;; bound → substitute value recursively
         (contains? v :val)
         (let [[t' ve' m'] (replace-vars-for-chs (:val v) loop-var-ids ve mapping)]
           [t' ve' (assoc m' t t')])

         ;; loop var → keep as-is
         (contains? loop-var-ids (get-value-id t ve))
         [t ve (assoc mapping t t)]

         ;; already seen this var → reuse same replacement
         (contains? mapping t)
         [(get mapping t) ve mapping]

         ;; unbound non-loop → freeze with fresh var
         :else
         (let [[fresh ve1] (generate-unique-var t ve)
               frozen      (assoc v :bindable? false)
               ve2         (update-var-value fresh frozen ve1)]
           [fresh ve2 (assoc mapping t fresh)])))

     (term/is-compound? t)
     (reduce (fn [[t-acc ve-acc m-acc] arg]
               (let [[arg' ve' m'] (replace-vars-for-chs arg loop-var-ids ve-acc m-acc)]
                 [(update t-acc :args conj arg') ve' m']))
             [(assoc t :args []) ve mapping]
             (:args t))

     :else [t ve mapping])))

(defn replace-args-for-chs
  "Apply replace-vars-for-chs to each arg in args.
   loop-var-set is a collection of variable names that are loop variables.
   Returns [args' updated-ve]."
  [args loop-var-set ve]
  (let [loop-ids (into #{} (keep #(get-value-id % ve)) loop-var-set)]
    (reduce (fn [[acc-args acc-ve acc-map] arg]
              (let [[arg' ve' m'] (replace-vars-for-chs arg loop-ids acc-ve acc-map)]
                [(conj acc-args arg') ve' m']))
            [[] ve {}]
            args)))

;;; ── Body-only variable extraction ───────────────────────────────────────────

(defn body-vars
  "Variables in body terms that do not appear in head-term."
  [head body]
  (vec (set/difference (term/terms-vars body) (term/term-vars head))))

;;; ── Resolve a term through var-env ──────────────────────────────────────────

(defn resolve-term
  "Follow variable bindings in ve to produce the most specific term.
   Does not recurse into compound args (shallow)."
  [t ve]
  (if (term/is-var? t)
    (let [v (var-value t ve)]
      (if (contains? v :val)
        (recur (:val v) ve)
        t))
    t))

(defn fill-in
  "Deeply substitute variable values from ve into term t."
  [t ve]
  (cond
    (term/is-var? t)
    (let [v (var-value t ve)]
      (if (contains? v :val)
        (recur (:val v) ve)
        t))
    (term/is-compound? t)
    (update t :args (fn [args] (mapv #(fill-in % ve) args)))
    :else t))
