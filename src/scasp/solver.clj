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


;;; ── CLP(R) symbolic constraint helpers ──────────────────────────────────────

(defn- resolve-arith
  "Try to evaluate t as a ground arithmetic value.
   Returns the number, or [::unbound var-name] if t reduces to a single unbound var,
   or [::linear coeff var-name offset] for affine expressions (coeff*var + offset),
   or throws for non-linear or otherwise unevaluable expressions."
  [t ve]
  (cond
    (number? t) t
    (term/is-var? t)
    (let [v (vars/var-value t ve)]
      (if (contains? v :val)
        (recur (:val v) ve)
        [::unbound t]))
    (term/is-compound? t)
    (let [op  (:op t)
          a1  (first  (:args t))
          a2  (second (:args t))
          r1  (when a1 (resolve-arith a1 ve))
          r2  (when a2 (resolve-arith a2 ve))
          lin? (fn [r] (and (vector? r) (= (first r) ::linear)))
          unb? (fn [r] (and (vector? r) (= (first r) ::unbound)))]
      (cond
        ;; Both ground — evaluate directly
        (and (number? r1) (number? r2))
        (let [va r1 vb r2]
          (cond
            (= op :+)    (+ va vb)
            (= op :-)    (if a2 (- va vb) (- va))
            (= op :*)    (* va vb)
            (= op :div)  (/ va vb)
            (= op :idiv) (quot va vb)
            (= op :rem)  (rem va vb)
            (= op :mod)  (mod va vb)
            (= op :<<)   (bit-shift-left  (long va) (int vb))
            (= op :>>)   (bit-shift-right (long va) (int vb))
            (= op :pow)  (Math/pow (double va) (double vb))
            (= op :hat)  (Math/pow (double va) (double vb))
            (= op :abs)  (Math/abs (double va))
            (= op :max)  (max va vb)
            (= op :min)  (min va vb)
            (= op :float)   (double va)
            (= op :integer) (long va)
            :else (throw (ex-info "Unknown arithmetic operator" {:op op}))))

        ;; Unary ground case (abs/float/integer/unary minus)
        (and (number? r1) (nil? r2))
        (case op
          :abs     (Math/abs (double r1))
          :float   (double r1)
          :integer (long r1)
          :- (- r1)
          (throw (ex-info "Unknown unary operator" {:op op})))

        ;; Affine: var + number  /  number + var
        (and (unb? r1) (number? r2) (= op :+)) [::linear 1 (second r1) r2]
        (and (number? r1) (unb? r2) (= op :+)) [::linear 1 (second r2) r1]
        ;; var - number
        (and (unb? r1) (number? r2) (= op :-)) [::linear 1 (second r1) (- r2)]
        ;; number - var  →  -1*var + number
        (and (number? r1) (unb? r2) (= op :-)) [::linear -1 (second r2) r1]
        ;; number * var  /  var * number
        (and (number? r1) (unb? r2) (= op :*)) [::linear r1 (second r2) 0]
        (and (unb? r1) (number? r2) (= op :*)) [::linear r2 (second r1) 0]
        ;; linear + number  /  number + linear
        (and (lin? r1) (number? r2) (= op :+))
        (let [[_ c v k] r1] [::linear c v (+ k r2)])
        (and (number? r1) (lin? r2) (= op :+))
        (let [[_ c v k] r2] [::linear c v (+ r1 k)])
        ;; linear - number
        (and (lin? r1) (number? r2) (= op :-))
        (let [[_ c v k] r1] [::linear c v (- k r2)])
        ;; number * linear
        (and (number? r1) (lin? r2) (= op :*))
        (let [[_ c v k] r2] [::linear (* r1 c) v (* r1 k)])
        (and (lin? r1) (number? r2) (= op :*))
        (let [[_ c v k] r1] [::linear (* c r2) v (* k r2)])

        :else (throw (ex-info "Non-linear or unevaluable expression" {:term t :r1 r1 :r2 r2}))))
    :else (throw (ex-info "Non-numeric term in arithmetic" {:term t}))))

(defn- unbound-var?
  "Return the var name if r is an [::unbound var] sentinel, else nil."
  [r]
  (when (and (vector? r) (= (first r) ::unbound)) (second r)))

(defn- clp-op->bound-op
  "Map a CLP(R) op keyword to the canonical comparison op used by add-numeric-bound."
  [op]
  (case op
    (:clp< :hash<)   :<
    (:clp> :hash>)   :>
    (:clp=< :hash=<) :=<
    (:clp>= :hash>=) :>=
    (:clp= :hash=)   :=:=
    (:clp<> :hash<>) :arith-ne
    op))

(defn- solve-clp-constraint
  "Handle a CLP(R) or classic comparison op when one or both sides may be unbound.
   clp-op is the raw op keyword (e.g. :clp< or :<).
   Returns updated ve or nil on failure."
  [clp-op lhs rhs ve]
  (let [r1 (try (resolve-arith lhs ve) (catch clojure.lang.ExceptionInfo _ nil))
        r2 (try (resolve-arith rhs ve) (catch clojure.lang.ExceptionInfo _ nil))
        uv1 (when r1 (unbound-var? r1))
        uv2 (when r2 (unbound-var? r2))
        bound-op (clp-op->bound-op clp-op)]
    (cond
      ;; Both ground → evaluate directly
      (and (number? r1) (number? r2))
      (case bound-op
        :<       (when (<  r1 r2) ve)
        :>       (when (>  r1 r2) ve)
        :=<      (when (<= r1 r2) ve)
        :>=      (when (>= r1 r2) ve)
        :=:=     (when (== r1 r2) ve)
        :arith-ne (when (not (== r1 r2)) ve)
        nil)

      ;; lhs is unbound var, rhs is ground → add bound on lhs
      (and uv1 (number? r2))
      (vars/add-numeric-bound uv1 bound-op r2 ve)

      ;; rhs is unbound var, lhs is ground → flip the constraint onto rhs
      (and (number? r1) uv2)
      (let [flipped (case bound-op
                      :<       :>
                      :>       :<
                      :=<      :>=
                      :>=      :=<
                      :=:=     :=:=
                      :arith-ne :arith-ne
                      nil)]
        (when flipped (vars/add-numeric-bound uv2 flipped r1 ve)))

      ;; Both unbound — record relational constraint on lhs referencing rhs,
      ;; and the flipped constraint on rhs referencing lhs
      (and uv1 uv2)
      (let [flipped (case bound-op
                      :<  :>  :>  :<  :=<  :>=  :>=  :=<
                      :=:= :=:=  :arith-ne :arith-ne  nil)
            ve' (vars/add-var-relational-constraint uv1 bound-op uv2 ve)]
        (if (and ve' flipped)
          (vars/add-var-relational-constraint uv2 flipped uv1 ve')
          ve'))

      :else nil)))

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
              (let [lhs (first args)
                    r2  (try (resolve-arith (second args) ve)
                             (catch clojure.lang.ExceptionInfo _ nil))]
                (cond
                  (number? r2)
                  (when-let [ve' (unify/solve-unify lhs r2 ve false)]
                    ve')
                  ;; rhs is a single unbound var → defer as equality
                  (and r2 (unbound-var? r2))
                  (solve-clp-constraint :=:= lhs (second args) ve)
                  ;; rhs is affine: coeff*Y + offset → store linear-eq on X and Y
                  (and r2 (vector? r2) (= (first r2) ::linear))
                  (let [[_ coeff y-var offset] r2]
                    (vars/add-linear-eq lhs coeff y-var offset ve))
                  :else nil))
              (= op :=:=)
              (solve-clp-constraint :=:= (first args) (second args) ve)
              (= op :arith-ne)     ; =\=
              (solve-clp-constraint :arith-ne (first args) (second args) ve)
              (= op :<)
              (solve-clp-constraint :< (first args) (second args) ve)
              (= op :>)
              (solve-clp-constraint :> (first args) (second args) ve)
              (= op :=<)
              (solve-clp-constraint :=< (first args) (second args) ve)
              (= op :>=)
              (solve-clp-constraint :>= (first args) (second args) ve)
              ;; CLP(R) symbolic operators (.<. .>. etc.) and #-aliases
              (contains? #{:clp< :clp> :clp=< :clp>= :clp= :clp<>
                           :hash= :hash< :hash> :hash>= :hash=< :hash<>} op)
              (solve-clp-constraint op (first args) (second args) ve)
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
                    r2    (try (resolve-arith (second (:args inner)) ve)
                               (catch clojure.lang.ExceptionInfo _ nil))]
                (when (number? r2)
                  (unify/solve-dnunify (first (:args inner)) r2 ve)))
              :else nil)]
        (when result
          [{:var-env result :just goal}]))
      (catch clojure.lang.ExceptionInfo _
        []))))

;;; ── Forall solver ────────────────────────────────────────────────────────────

(defn- solve-forall3
  "Re-verify Goal with V bound, in turn, to each value in vals, THREADING the
   var-env through the sequence (mirrors solve_forall3/11 in solve.pl).

   Threading the var-env is load-bearing: re-verifying V=val may succeed only by
   constraining ANOTHER (outer) universally-quantified variable, and those
   constraints must propagate so the enclosing forall can in turn check the
   values it now excludes.  The CHS is NOT threaded between values: each value's
   body proof is an INDEPENDENT coinductive derivation and must start from the
   entry CHS, else one value's success entries grant a sibling spurious
   coinductive success.  Returns a (possibly empty) seq; empty means some value
   had no solution → the universal claim over V fails."
  [v-name vals goal ve chs call-stack in-nmr? program]
  (if (empty? vals)
    [(mk-result ve chs :success [])]
    (let [g2 (term/substitute v-name (first vals) goal)]
      (mapcat
        (fn [{ve' :var-env el :even-loops}]
          (map (fn [r] (update r :even-loops into el))
               (solve-forall3 v-name (rest vals) goal ve' chs
                              call-stack in-nmr? program)))
        (solve-goals [g2] ve chs call-stack in-nmr? program)))))

(defn solve-forall
  "Solve forall(V, Goal) universally quantified over V.

   Mirrors solve_forall/solve_forall2/solve_forall3 in solve.pl:
   1. If V already bound, solve Goal normally.
   2. Mark V non-bindable and non-loop, then solve Goal once.
   3. After Goal succeeds:
      - V still unbound with no new constraints → universal success.
      - V acquired new disequality constraints (values it must not be)
        → must re-verify Goal holds with V bound to each of those values,
          THREADING any constraints picked up on other forall variables.
      - V got bound → fail (forall requires V to remain free).

   Before anything else V (and its occurrences in Goal) is alpha-renamed to a
   fresh variable — mirrors `my_copy_term(Var, Goal, …)` in solve.pl.  Without
   this, a nested or repeated forall that reuses the same source variable name
   inherits residual disequality constraints left in the var-env by an earlier
   forall over that name, so its \"new constraints\" set comes out empty and it
   wrongly reports universal success."
  [v-name0 goal0 ve chs call-stack in-nmr? program]
  (let [[v-name ve*] (vars/generate-unique-var v-name0 ve)
        goal          (term/substitute v-name0 v-name goal0)
        ve            ve*
        orig-cs (vars/is-unbound? v-name ve)]
    (if-not orig-cs
      ;; V already bound → solve goal normally
      (solve-goals [goal] ve chs call-stack in-nmr? program)
      ;; V unbound: mark non-bindable + non-loop, then solve Goal once
      (let [marked (assoc orig-cs :bindable? false :loop-var -1)
            ve1    (vars/update-var-value v-name marked ve)
            body-results (solve-goals [goal] ve1 chs call-stack in-nmr? program)]
        ;; If Goal has no solution with V free, the universal claim fails.
        ;; (Mirrors Ciao solve_forall, where a failing solve_goals fails the
        ;; whole forall.  There is NO vacuous-truth success: a positive goal
        ;; that holds only by binding V means "for all V, G" is false.  The
        ;; genuine "always true" cases — e.g. not_q for an undefined q — already
        ;; produce a real solution with V free via their generated dual, so they
        ;; never reach this branch.)
        (if (empty? body-results)
          []
          (lazy-seq
            (mapcat
              (fn [{ve2 :var-env chs1 :chs just :just el :even-loops}]
                (let [cur-cs (vars/is-unbound? v-name ve2)]
                  (cond
                    ;; V still unbound with no new constraints → success
                    (and cur-cs (empty? (set/difference
                                          (:constraints cur-cs)
                                          (:constraints orig-cs))))
                    [(mk-result ve2 chs1 {:forall v-name :body just} el)]

                    ;; V acquired new disequality constraints → re-verify for
                    ;; each, threading constraints picked up on other forall vars
                    ;; so the enclosing forall sees them.  Re-verify against the
                    ;; CHS as it was on ENTRY to this forall (chs), not the
                    ;; post-first-solve chs1: each value check is an independent
                    ;; proof of the body, so the first solve's sibling success
                    ;; entries must not grant it spurious coinductive success.
                    cur-cs
                    (let [new-vals (set/difference
                                     (:constraints cur-cs)
                                     (:constraints orig-cs))]
                      (map (fn [{ve3 :var-env chs3 :chs el3 :even-loops}]
                             (mk-result ve3 chs3 {:forall v-name :body just}
                                        (into el el3)))
                           (solve-forall3 v-name (vec new-vals) goal
                                          ve2 chs call-stack in-nmr? program)))

                    ;; V got bound → fail
                    :else [])))
              body-results)))))))

;;; ── Goal dispatcher ──────────────────────────────────────────────────────────

(defn- prepend-just
  "Cons j1 onto j2, producing a flat sequence of justification nodes."
  [j1 j2]
  (cond
    (or (nil? j1) (= j1 :success)) j2
    (or (nil? j2) (= j2 :success)) j1
    (sequential? j2)               (into [j1] j2)
    :else                          [j1 j2]))

(defn- solve-goals*
  [goals ve chs call-stack in-nmr? even-loops program]
  (if (empty? goals)
    [(mk-result ve chs :success [])]
    (lazy-seq
      (mapcat
        (fn [{ve' :var-env chs' :chs just1 :just el :even-loops}]
          (let [el' (into even-loops el)]
            (map (fn [r2] (-> r2
                              (update :even-loops into el)
                              (update :just #(prepend-just just1 %))))
                 (solve-goals* (rest goals) ve' chs' call-stack in-nmr? el' program))))
        (solve-goal (first goals) ve chs call-stack in-nmr? even-loops program)))))

(defn solve-goals
  "Solve a list of goals.  Returns lazy-seq of result maps."
  [goals ve chs call-stack in-nmr? program]
  (solve-goals* goals ve chs call-stack in-nmr? [] program))

;;; ── findall/3 ────────────────────────────────────────────────────────────────

(defn- solve-findall
  "findall(Template, Goal, List): collect all Template instances for which Goal
   succeeds into List.  Always succeeds (returns [] if Goal fails)."
  [template goal-term list-arg ve chs call-stack in-nmr? program]
  (let [solutions (solve-goals [goal-term] ve chs call-stack in-nmr? program)
        bag       (mapv (fn [{ve' :var-env}]
                          (vars/fill-in template ve'))
                        solutions)
        ;; Build a Prolog-style list term from bag
        list-term (reduce (fn [acc item]
                            {:op :cons :args [item acc]})
                          (keyword "[]")
                          (reverse bag))]
    (when-let [ve' (unify/solve-unify list-arg list-term ve false)]
      [(mk-result ve' chs {:findall template} [])])))

;;; ── Effect builtins ──────────────────────────────────────────────────────────

(def ^:private effect-ops
  #{:print :println :nl :read_line :read_number
    :string_concat :string_length :atom_string
    :write_file :read_file :append_file :file_exists})

(defn- effect-term-str
  "Convert a resolved term to a printable string for effect output."
  [t ve]
  (let [t' (vars/fill-in t ve)]
    (cond
      (term/is-string-val? t') (term/string-val-str t')
      (keyword? t')            (name t')
      (number? t')             (str t')
      (string? t')             t'
      (term/is-compound? t')   (term/pp-term t')
      :else                    (str t'))))

(defn- solve-effect
  "Execute an effect goal. Returns seq of result maps (empty = failure)."
  [goal ve chs]
  (let [op   (:op goal)
        args (:args goal)]
    (case op
      :print
      (do (print (effect-term-str (first args) ve))
          (flush)
          [(mk-result ve chs :success [])])

      :println
      (do (println (effect-term-str (first args) ve))
          [(mk-result ve chs :success [])])

      :nl
      (do (println)
          [(mk-result ve chs :success [])])

      :read_line
      (if-let [line (read-line)]
        (when-let [ve' (unify/solve-unify (first args) (term/string-val line) ve false)]
          [(mk-result ve' chs :success [])])
        [])

      :read_number
      (try
        (let [line (clojure.string/trim (or (read-line) ""))
              n    (if (clojure.string/includes? line ".")
                     (Double/parseDouble line)
                     (Long/parseLong line))]
          (when-let [ve' (unify/solve-unify (first args) n ve false)]
            [(mk-result ve' chs :success [])]))
        (catch Exception _ []))

      :string_concat
      (let [[a b c] args
            sa     (effect-term-str a ve)
            sb     (effect-term-str b ve)
            result (term/string-val (str sa sb))]
        (when-let [ve' (unify/solve-unify c result ve false)]
          [(mk-result ve' chs :success [])]))

      :string_length
      (let [s (effect-term-str (first args) ve)
            n (long (count s))]
        (when-let [ve' (unify/solve-unify (second args) n ve false)]
          [(mk-result ve' chs :success [])]))

      :atom_string
      (let [[a s] args
            av (vars/fill-in a ve)
            sv (vars/fill-in s ve)]
        (cond
          (keyword? av)
          (when-let [ve' (unify/solve-unify s (term/string-val (name av)) ve false)]
            [(mk-result ve' chs :success [])])
          (term/is-string-val? sv)
          (when-let [ve' (unify/solve-unify a (keyword (term/string-val-str sv)) ve false)]
            [(mk-result ve' chs :success [])])
          :else []))

      :write_file
      (let [[path content] args]
        (spit (effect-term-str path ve) (effect-term-str content ve))
        [(mk-result ve chs :success [])])

      :read_file
      (try
        (let [content (slurp (effect-term-str (first args) ve))]
          (when-let [ve' (unify/solve-unify (second args) (term/string-val content) ve false)]
            [(mk-result ve' chs :success [])]))
        (catch Exception _ []))

      :append_file
      (let [[path content] args]
        (spit (effect-term-str path ve) (effect-term-str content ve) :append true)
        [(mk-result ve chs :success [])])

      :file_exists
      (if (.exists (java.io.File. (effect-term-str (first args) ve)))
        [(mk-result ve chs :success [])]
        [])

      (throw (ex-info (str "Unknown effect: " op) {:goal goal})))))

;;; ── Goal dispatcher ──────────────────────────────────────────────────────────

(defn solve-goal
  "Dispatch a single goal to the appropriate solver."
  [goal ve chs call-stack in-nmr? even-loops program]
  (cond
    ;; forall(V, G)
    (term/is-forall? goal)
    (let [[v g] (:args goal)]
      (solve-forall v g ve chs call-stack in-nmr? program))

    ;; findall(Template, Goal, List)
    (and (term/is-compound? goal) (= (:op goal) :findall) (= (count (:args goal)) 3))
    (let [[tmpl g lst] (:args goal)]
      (or (solve-findall tmpl g lst ve chs call-stack in-nmr? program) []))

    ;; call(Goal) or call(Goal, Arg…) — partial application
    (and (term/is-compound? goal) (= (:op goal) :call) (pos? (count (:args goal))))
    (let [called (vars/fill-in (first (:args goal)) ve)
          extra  (rest (:args goal))
          ;; If extra args, extend the called term's arg list
          effective (if (seq extra)
                      (if (term/is-compound? called)
                        (update called :args into extra)
                        (throw (ex-info "call/N: first arg must be compound" {:called called})))
                      called)]
      (solve-goal effective ve chs call-stack in-nmr? even-loops program))

    ;; true/0
    (and (term/is-compound? goal) (= (:op goal) :true) (empty? (:args goal)))
    [(mk-result ve chs :success [])]

    ;; false/0 or fail/0
    (and (term/is-compound? goal)
         (or (= (:op goal) :false) (= (:op goal) :fail))
         (empty? (:args goal)))
    []

    ;; Effect builtins (IO, string ops, file ops)
    (and (term/is-compound? goal) (contains? effect-ops (:op goal)))
    (or (solve-effect goal ve chs) [])

    ;; NAF over effect builtins: try the effect, negate the result
    (and (term/is-naf? goal)
         (let [inner (first (:args goal))]
           (and (term/is-compound? inner) (contains? effect-ops (:op inner)))))
    (let [inner  (first (:args goal))
          results (solve-effect inner ve chs)]
      (if (seq results)
        []
        [(mk-result ve chs :success [])]))

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
  "Solve a predicate goal (positive, NAF-wrapped, or strong-negation)."
  [goal ve chs call-stack in-nmr? even-loops program]
  (let [[functor args]
        (cond
          (term/is-naf? goal)
          (let [inner (first (:args goal))]
            [(term/negate-functor (term/term-functor inner)) (:args inner)])
          (term/is-sneg? goal)
          (let [inner (first (:args goal))]
            [(term/strong-negate-functor (term/term-functor inner)) (:args inner)])
          :else
          [(term/term-functor goal) (:args goal)])
        effective-goal
        (cond
          (term/is-naf? goal)
          (term/make-compound (term/functor-name-str functor) args)
          (term/is-sneg? goal)
          (term/make-compound (term/functor-name-str functor) args)
          :else goal)]
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
        goal-key         (if (empty? args) :nullary
                             (prog/index-key (vars/resolve-term (first args) ve)))
        rules            (prog/candidate-rules functor goal-key program)
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
                     (update r :just (fn [j] {:rule h2 :sub-just j})))
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
