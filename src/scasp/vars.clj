(ns scasp.vars
  "Variable environment: explicit union-find structure for s(CASP) variable management.

   var-env structure:
     {:names  {var-name → initial-id}    ; string → int
      :values {id       → var-value}      ; int    → map
      :name-cnt int                       ; counter for fresh variable names
      :id-cnt   int}                      ; counter for fresh value IDs

   var-value is one of:
     {:val v}                                             ; bound to value v
     {:constraints #{v1 …} :bindable? bool :loop-var n}  ; unbound/constrained
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

(def ^:private default-unbound {:constraints #{} :bindable? true :loop-var 0})

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
  "Check that ground value val does not violate any constraints.
   Returns ve unchanged on success, nil on violation."
  [constraints val ve]
  (if (contains? constraints val)
    nil
    ve))

(defn add-var-constraint
  "Add forbidden value c to var-name's constraint set.
   Returns updated ve or nil if variable is already bound."
  [var-name c ve]
  (when-let [cs (is-unbound? var-name ve)]
    (let [new-cs (update cs :constraints conj c)]
      (update-var-value var-name new-cs ve))))

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
      (let [cs1 (:constraints (is-unbound? v1 ve))
            cs2 (:constraints (is-unbound? v2 ve))
            f1  (:bindable?   (is-unbound? v1 ve))
            f2  (:bindable?   (is-unbound? v2 ve))
            lv1 (:loop-var    (is-unbound? v1 ve))
            lv2 (:loop-var    (is-unbound? v2 ve))
            merged {:constraints (set/union cs1 cs2)
                    :bindable?   (and f1 f2)
                    :loop-var    (merge-loop-var lv1 lv2)}
            ve1 (update-var-value v1 merged ve)
            fid (get-value-id v1 ve1)]
        (if id2
          (assoc-in ve1 [:values id2] {:link fid})
          (let [new-id (:id-cnt ve1)]
            (-> ve1
                (assoc-in [:names v2] new-id)
                (assoc-in [:values new-id] {:link fid})
                (update :id-cnt inc)))))

      ;; v1 unbound, v2 bound → link v1 → v2
      (is-unbound? v1 ve)
      (let [{:keys [constraints bindable?]} (is-unbound? v1 ve)]
        (when bindable?
          (let [val (:val (var-value v2 ve))]
            (when-let [ve' (test-constraints constraints val ve)]
              (let [fid2 (or id2 (do
                                   ;; v2 not yet in env but is bound — shouldn't normally happen
                                   (get-value-id v2 ve')))]
                (if fid2
                  (if id1
                    (assoc-in ve' [:values id1] {:link fid2})
                    (let [new-id (:id-cnt ve')]
                      (-> ve'
                          (assoc-in [:names v1] new-id)
                          (assoc-in [:values new-id] {:link fid2})
                          (update :id-cnt inc))))
                  ;; v2 was never in env; just bind v1 directly
                  (update-var-value v1 {:val val} ve')))))))

      ;; v2 unbound, v1 bound → link v2 → v1
      (is-unbound? v2 ve)
      (let [{:keys [constraints bindable?]} (is-unbound? v2 ve)]
        (when bindable?
          (let [val (:val (var-value v1 ve))]
            (when-let [ve' (test-constraints constraints val ve)]
              (if id1
                (if id2
                  (assoc-in ve' [:values id2] {:link id1})
                  (let [new-id (:id-cnt ve')]
                    (-> ve'
                        (assoc-in [:names v2] new-id)
                        (assoc-in [:values new-id] {:link id1})
                        (update :id-cnt inc))))
                (update-var-value v2 {:val val} ve'))))))

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
