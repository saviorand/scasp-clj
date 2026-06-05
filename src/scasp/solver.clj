(ns scasp.solver
  "Core s(CASP) solver.

   Every solve-* function returns a lazy sequence of result maps:
     {:var-env  <updated var-env>
      :chs      <updated CHS>
      :just     <justification tree node>
      :even-loops [cycle…]}

   An empty sequence means failure.  Backtracking = taking the next element."
  (:require [clojure.set   :as set]
            [scasp.term    :as term]
            [scasp.vars    :as vars]
            [scasp.unify   :as unify]
            [scasp.program :as prog]
            [scasp.chs     :as chs]))

;;; Forward declarations (mutual recursion between solve functions)
(declare solve-goal solve-goals solve-goals* solve-predicate expand-call expand-call2)

(defn- collect-cvars
  "Flatten all cvars from a list of even-loop entries [{:cycle … :cvars […]} …]."
  [even-loops]
  (into [] (mapcat :cvars) even-loops))

;;; ── Result record helper ─────────────────────────────────────────────────────

(defn- mk-result [ve ch just el]
  {:var-env ve :chs ch :just just :even-loops el})

;;; ── Arithmetic sub-expression evaluator ─────────────────────────────────────

(defn solve-subexpr
  "Evaluate an arithmetic expression, returning its ground numeric value."
  [t ve]
  (cond
    (number? t) t
    (term/is-var? t)
    (let [v (vars/var-value t ve)]
      (if (contains? v :val)
        (recur (:val v) ve)
        (throw (ex-info "Unbound variable in arithmetic" {:var t}))))
    (term/is-compound? t)
    (let [op   (:op t)
          a1   (first  (:args t))
          a2   (second (:args t))
          va   (when a1 (solve-subexpr a1 ve))
          vb   (when a2 (solve-subexpr a2 ve))]
      (cond
        (= op :+)    (+ va vb)
        (= op :-)    (if a2 (- va vb) (- va))
        (= op :*)    (* va vb)
        (= op :div)  (/ va vb)          ; Prolog /
        (= op :idiv) (quot va vb)       ; Prolog //
        (= op :rem)  (rem va vb)
        (= op :mod)  (mod va vb)
        (= op :<<)   (bit-shift-left  (long va) (int vb))
        (= op :>>)   (bit-shift-right (long va) (int vb))
        (= op :pow)  (Math/pow (double va) (double vb))   ; Prolog **
        (= op :hat)  (Math/pow (double va) (double vb))   ; Prolog ^
        (= op :abs)  (Math/abs (double va))
        (= op :max)  (max va vb)
        (= op :min)  (min va vb)
        (= op :float)   (double va)
        (= op :integer) (long va)
        :else (throw (ex-info "Unknown arithmetic operator" {:op op}))))
    :else (throw (ex-info "Non-numeric term in arithmetic" {:term t}))))

;;; ── Expression solver ────────────────────────────────────────────────────────

(defn solve-expression
  "Solve a built-in arithmetic/comparison goal.
   Returns lazy-seq of {:var-env :just} maps (no chs change)."
  [goal ve]
  (let [op   (:op goal)
        args (:args goal)]
    (try
      (let [result
            (cond
              (= op :=)
              (when-let [ve' (unify/solve-unify (first args) (second args) ve false)]
                ve')
              (= op :ne)          ; \=
              (when-let [ve' (unify/solve-dnunify (first args) (second args) ve)]
                ve')
              (= op :is)
              (let [rhs (solve-subexpr (second args) ve)]
                (when-let [ve' (unify/solve-unify (first args) rhs ve false)]
                  ve'))
              (= op :=:=)
              (let [v1 (solve-subexpr (first args) ve)
                    v2 (solve-subexpr (second args) ve)]
                (when (== v1 v2) ve))
              (= op :arith-ne)     ; =\=
              (let [v1 (solve-subexpr (first args) ve)
                    v2 (solve-subexpr (second args) ve)]
                (when (not (== v1 v2)) ve))
              (= op :<)
              (let [v1 (solve-subexpr (first args) ve)
                    v2 (solve-subexpr (second args) ve)]
                (when (< v1 v2) ve))
              (= op :>)
              (let [v1 (solve-subexpr (first args) ve)
                    v2 (solve-subexpr (second args) ve)]
                (when (> v1 v2) ve))
              (= op :=<)
              (let [v1 (solve-subexpr (first args) ve)
                    v2 (solve-subexpr (second args) ve)]
                (when (<= v1 v2) ve))
              (= op :>=)
              (let [v1 (solve-subexpr (first args) ve)
                    v2 (solve-subexpr (second args) ve)]
                (when (>= v1 v2) ve))
              (= op :term<)
              (let [v1 (vars/fill-in (first args) ve)
                    v2 (vars/fill-in (second args) ve)]
                (when (neg? (compare v1 v2)) ve))
              (= op :term>)
              (let [v1 (vars/fill-in (first args) ve)
                    v2 (vars/fill-in (second args) ve)]
                (when (pos? (compare v1 v2)) ve))
              (= op :term<=)
              (let [v1 (vars/fill-in (first args) ve)
                    v2 (vars/fill-in (second args) ve)]
                (when (not (pos? (compare v1 v2))) ve))
              (= op :term>=)
              (let [v1 (vars/fill-in (first args) ve)
                    v2 (vars/fill-in (second args) ve)]
                (when (not (neg? (compare v1 v2))) ve))
              ;; not(is(X,E)) → disequality on arithmetic result
              (and (= op :not)
                   (let [inner (first args)]
                     (and (term/is-compound? inner) (= (:op inner) :is))))
              (let [inner (first args)
                    rhs   (solve-subexpr (second (:args inner)) ve)]
                (unify/solve-dnunify (first (:args inner)) rhs ve))
              :else nil)]
        (when result
          [{:var-env result :just goal}]))
      (catch clojure.lang.ExceptionInfo _
        []))))

;;; ── Forall solver ────────────────────────────────────────────────────────────

(defn solve-forall
  "Solve forall(V, Goal) universally quantified over V."
  [v-name goal ve chs call-stack in-nmr? program]
  (let [orig-cs (vars/is-unbound? v-name ve)]
    (if-not orig-cs
      ;; V already bound → solve goal normally
      (solve-goals [goal] ve chs call-stack in-nmr? program)
      ;; V unbound: mark non-bindable + non-loop
      (let [marked (assoc orig-cs :bindable? false :loop-var -1)
            ve1    (vars/update-var-value v-name marked ve)
            body-results (solve-goals [goal] ve1 chs call-stack in-nmr? program)]
        ;; Vacuous truth: goal produces no solutions → forall trivially succeeds
        (if (empty? body-results)
          [(mk-result ve chs {:forall v-name :body :vacuous} [])]
          (lazy-seq
            (mapcat
              (fn [{ve2 :var-env chs1 :chs just :just el :even-loops}]
                (let [cur-cs (vars/is-unbound? v-name ve2)]
                  (cond
                    ;; Still unbound (no constraints acquired) → success
                    (and cur-cs (empty? (:constraints cur-cs)))
                    [(mk-result ve2 chs1 {:forall v-name :body just} el)]

                    ;; Acquired constraints → must succeed for each value
                    (and cur-cs (seq (:constraints cur-cs)))
                    (let [new-vals (set/difference
                                    (:constraints cur-cs)
                                    (:constraints orig-cs))]
                      (if (empty? new-vals)
                        [(mk-result ve2 chs1 {:forall v-name :body just} el)]
                        (when (every? (fn [val]
                                        (let [ve3 (vars/update-var-value v-name {:val val} ve2)
                                              g2  (term/substitute v-name val goal)]
                                          (seq (solve-goals [g2] ve3 chs1 call-stack in-nmr? program))))
                                      new-vals)
                          [(mk-result ve2 chs1 {:forall v-name :body just} el)])))
                    ;; V got bound → fail
                    :else [])))
              body-results)))))))

;;; ── Goal dispatcher ──────────────────────────────────────────────────────────

(defn- solve-goals*
  [goals ve chs call-stack in-nmr? even-loops program]
  (if (empty? goals)
    [(mk-result ve chs :success [])]
    (lazy-seq
      (mapcat
        (fn [{ve' :var-env chs' :chs el :even-loops}]
          (let [el' (into even-loops el)]
            (map (fn [r2] (update r2 :even-loops into el))
                 (solve-goals* (rest goals) ve' chs' call-stack in-nmr? el' program))))
        (solve-goal (first goals) ve chs call-stack in-nmr? even-loops program)))))

(defn solve-goals
  "Solve a list of goals.  Returns lazy-seq of result maps."
  [goals ve chs call-stack in-nmr? program]
  (solve-goals* goals ve chs call-stack in-nmr? [] program))

(defn solve-goal
  "Dispatch a single goal to the appropriate solver."
  [goal ve chs call-stack in-nmr? even-loops program]
  (cond
    ;; forall(V, G)
    (term/is-forall? goal)
    (let [[v g] (:args goal)]
      (solve-forall v g ve chs call-stack in-nmr? program))

    ;; Arithmetic / comparison expression
    (term/is-expr? goal)
    (map (fn [{ve' :var-env just :just}]
           (mk-result ve' chs just []))
         (solve-expression goal ve))

    ;; NAF or regular predicate
    (term/is-compound? goal)
    (solve-predicate goal ve chs call-stack in-nmr? even-loops program)

    :else
    (throw (ex-info "Unknown goal type" {:goal goal}))))

;;; ── Predicate solver ─────────────────────────────────────────────────────────

(defn solve-predicate
  "Solve a predicate goal (positive or NAF-wrapped)."
  [goal ve chs call-stack in-nmr? even-loops program]
  (let [[functor args]
        (if (term/is-naf? goal)
          (let [inner (first (:args goal))]
            [(term/negate-functor (term/term-functor inner)) (:args inner)])
          [(term/term-functor goal) (:args goal)])
        effective-goal
        (if (term/is-naf? goal)
          (term/make-compound (term/functor-name-str functor) args)
          goal)]
    (lazy-seq
      (mapcat
        (fn [{:keys [result var-env even-loop]}]
          (case result
            :coinductive-success
            [(mk-result var-env chs {:chs-success goal}
                        (if even-loop [even-loop] []))]
            :not-present
            (expand-call effective-goal functor args var-env chs call-stack in-nmr? even-loops program)
            []))
        (chs/check-chs functor args ve chs call-stack)))))

;;; ── Rule expansion ───────────────────────────────────────────────────────────

(defn expand-call
  "Expand a predicate call by looking up rules and trying each.
   If the functor is abducible and has no rules, succeed with goal added to CHS."
  [goal functor args ve chs call-stack in-nmr? even-loops program]
  (let [cvars            (collect-cvars even-loops)
        [entry chs1 ve1] (chs/add-to-chs functor args false in-nmr? chs ve cvars)
        rules            (prog/defined-rules functor program)
        new-stack        (into [{:goal goal :rule nil}] call-stack)]
    (if (and (empty? rules) (prog/abducible? functor program))
      ;; Abducible with no rules: succeed, recording goal as assumed true
      (let [chs2          (chs/remove-from-chs entry functor chs1)
            [_ chs3 _ve3] (chs/add-to-chs functor args true in-nmr? chs2 ve1 cvars)]
        [(mk-result ve1 chs3 {:abduced goal} [])])
      (lazy-seq
        (mapcat
          (fn [{ve2 :var-env chs2 :chs just :just el :even-loops}]
            (let [chs3           (chs/remove-from-chs entry functor chs2)
                  [_ chs4 _ve4]  (chs/add-to-chs functor args true in-nmr? chs3 ve2 cvars)]
              [(mk-result ve2 chs4 just el)]))
          (expand-call2 goal rules ve1 chs1 new-stack in-nmr? program))))))

(defn expand-call2
  "Try each rule in turn; yield results for matching rules."
  [goal rules ve chs call-stack in-nmr? program]
  (if (empty? rules)
    []
    (lazy-seq
      (let [{:keys [head body]} (first rules)]
        (concat
          ;; Try this rule
          (let [[h2 b2 ve'] (vars/get-unique-vars head body ve)
                ve''        (unify/solve-unify goal h2 ve' false)]
            (when ve''
              (map (fn [r]
                     (update r :just (fn [j] {:rule head :sub-just j})))
                   (solve-goals b2 ve'' chs call-stack in-nmr? program))))
          ;; Try remaining rules
          (expand-call2 goal (rest rules) ve chs call-stack in-nmr? program))))))

;;; ── DCC (Denial Consistency Check) ──────────────────────────────────────────

(defn- run-dcc
  "Post-query check for integrity constraints with variables.
   For each _false/0 rule, solve its body with fresh alpha-renamed vars
   against the result's var-env and chs. If any body succeeds, fail the branch.
   Abducibles are disabled during DCC — only existing rules and CHS entries count."
  [result program]
  (let [false-rules (prog/defined-rules "_false/0" program)]
    (if (empty? false-rules)
      [result]
      (let [{:keys [var-env chs]} result
            ;; Run DCC against the result's CHS so abduced facts are visible,
            ;; but strip abducibles to prevent new abductions during the check.
            dcc-program (assoc program :abducibles #{})]
        (if (every? (fn [{:keys [head body]}]
                      (let [[_ renamed-body ve'] (vars/get-unique-vars head body var-env)
                            solutions (solve-goals renamed-body ve' chs [] false dcc-program)]
                        (empty? solutions)))
                    false-rules)
          [result]
          [])))))

;;; ── Top-level entry ──────────────────────────────────────────────────────────

(defn run-query
  "Run the program query with NMR check, then apply DCC.
   Returns a lazy sequence of {:var-env :chs :just :even-loops}."
  [program]
  (let [query  (prog/defined-query program)
        nmr    (prog/defined-nmr-check program)
        goals  (into (vec query) nmr)
        ve     (vars/new-var-env)
        ch     (chs/new-chs)]
    (mapcat #(run-dcc % program)
            (solve-goals goals ve ch [] false program))))
