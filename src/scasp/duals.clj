(ns scasp.duals
  "Dual rule compilation.

   For each user-defined predicate p/n, generate rules for not_p/n
   that implement the negation-as-failure semantics without grounding.

   Algorithm (mirrors comp_duals.pl):
   1. outer-dual-head  – create not_p(A0,A1,…) with fresh variable args
   2. abstract-structures – replace compound head args with vars + unif goals
   3. prep-args        – determine which head args need unification goals
   4. comp-dual3       – one inner-dual clause per body goal (keep prior goals +
                         negate current)
   5. comp-dual2       – wrap body-only vars in forall
   6. comp-dual        – assemble per-clause duals + outer not_p clause
   7. compile-duals    – iterate over all predicates"
  (:require [scasp.term    :as term]
            [scasp.vars    :as vars]
            [scasp.program :as prog]))

;;; ── Goal negation ────────────────────────────────────────────────────────────

(def ^:private effect-builtin-ops
  #{:print :println :nl :read_line :read_number
    :string_concat :string_length :atom_string
    :write_file :read_file :append_file :file_exists
    :now_hour :now_minute :now_second :now_timestamp :now_date
    :env_var :random_int :format_number :clj_call})

(defn dual-goal
  "Negate a single goal for use in a dual clause body."
  [g]
  (cond
    (term/is-sneg? g)
    (first (:args g))

    (term/is-naf? g)
    (first (:args g))

    (term/is-compound? g)
    (let [op (:op g)]
      (cond
        (contains? effect-builtin-ops op) {:op :not :args [g]}
        :else
        (case op
          :=        (assoc g :op :ne)
          :ne       (assoc g :op :=)
          :=:=      (assoc g :op :arith-ne)
          :arith-ne (assoc g :op :=:=)
          :<        (assoc g :op :>=)
          :>        (assoc g :op :=<)
          :=<       (assoc g :op :>)
          :>=       (assoc g :op :<)
          :term<    (assoc g :op :term>=)
          :term>    (assoc g :op :term<=)
          :term<=   (assoc g :op :term>)
          :term>=   (assoc g :op :term<)
          :clp<     (assoc g :op :clp>=)
          :clp>     (assoc g :op :clp=<)
          :clp=<    (assoc g :op :clp>)
          :clp>=    (assoc g :op :clp<)
          :clp=     (assoc g :op :clp<>)
          :clp<>    (assoc g :op :clp=)
          :hash<    (assoc g :op :hash>=)
          :hash>    (assoc g :op :hash=<)
          :hash=<   (assoc g :op :hash>)
          :hash>=   (assoc g :op :hash<)
          :hash=    (assoc g :op :hash<>)
          :hash<>   (assoc g :op :hash=)
          :is       {:op :not :args [g]}
          (assoc g :op (keyword (str "not_" (name op)))))))

    :else {:op :not :args [g]}))

;;; ── Outer dual head ──────────────────────────────────────────────────────────

(defn outer-dual-head
  "Given a compound head like p(X,Y), produce not_p(_A0,_A1)."
  [head]
  (let [f    (term/term-functor head)
        df   (term/negate-functor f)
        n    (term/functor-arity f)
        args (prog/var-list n)]
    (term/make-compound (term/functor-name-str df) args)))

;;; ── Argument abstraction ─────────────────────────────────────────────────────

(defn abstract-structures
  "Replace compound args in the head arg list with fresh variables,
   returning [new-args unification-goals counter]."
  [args counter]
  (reduce (fn [[new-args goals c] a]
            (if (and (term/is-compound? a) (not (term/is-naf? a)))
              (let [vname (str "_Z" c)]
                [(conj new-args vname)
                 (conj goals (term/make-compound "=" [vname a]))
                 (inc c)])
              [(conj new-args a) goals c]))
          [[] [] counter]
          args))

;;; ── Prep-args ────────────────────────────────────────────────────────────────

(defn prep-args
  "Given original head args and variable-args (same length),
   produce [final-args unification-goals] for the inner-dual head.
   Variables in original that haven't been seen are kept; repeated variables
   and non-variables get the corresponding var-arg with a unification goal."
  [orig-args var-args]
  (let [[result goals _seen]
        (reduce (fn [[res goals seen] [oa va]]
                  (cond
                    ;; original is a fresh variable not yet seen
                    (and (term/is-var? oa) (not (contains? seen oa)))
                    [(conj res oa) goals (conj seen oa)]
                    ;; repeated variable or non-variable → use var-arg + unif goal
                    :else
                    [(conj res va)
                     (conj goals (term/make-compound "=" [va oa]))
                     seen]))
                [[] [] #{}]
                (map vector orig-args var-args))]
    [result goals]))

;;; ── Inner dual (comp-dual3) ──────────────────────────────────────────────────

(defn- comp-dual3
  "Generate inner-dual clauses for a single rule.
   For each body goal gi, produce a rule:
     DualHead :- [prior-goals… dual(gi)]"
  [dual-head body acc-rules]
  (loop [remaining body used [] rules acc-rules]
    (if (empty? remaining)
      rules
      (let [g  (first remaining)
            dg (dual-goal g)
            body-for-clause (conj (vec used) dg)
            rule (prog/make-rule dual-head body-for-clause)]
        (recur (rest remaining) (conj used g) (conj rules rule))))))

;;; ── Forall wrapping (comp-dual2) ─────────────────────────────────────────────

(defn- define-forall
  "Wrap goal in nested forall for each body variable."
  [goal bvars]
  (reduce (fn [g v] (term/make-compound "forall" [v g]))
          goal
          (reverse bvars)))

;;; ── Full dual for one rule (comp-dual2 equivalent) ──────────────────────────

(defn comp-dual-for-clause
  "Compute the dual clauses for a single original rule, adding them to prog.
   Returns [inner-dual-head prog]."
  [outer-dual-head clause inner-counter prog]
  (let [{:keys [head body]} clause
        orig-args  (:args head)
        outer-args (:args outer-dual-head)
        [abst-args abst-goals _c] (abstract-structures orig-args 0)
        [prep-args-v prep-goals] (prep-args abst-args outer-args)
        full-body  (into (into (vec prep-goals) abst-goals) body)
        bvars      (vars/body-vars (assoc outer-dual-head :args prep-args-v) full-body)
        ;; build the inner dual head functor
        outer-name (name (:op outer-dual-head))
        inner-name (str "_" outer-name "_" inner-counter)
        inner-arity (count outer-args)
        inner-head (if (empty? bvars)
                     (term/make-compound inner-name prep-args-v)
                     (term/make-compound (str inner-name "_" (+ inner-arity (count bvars)))
                                         (into (vec prep-args-v) bvars)))]
    (if (empty? bvars)
      ;; No body-only vars: just generate inner-dual clauses
      (let [rules (comp-dual3 inner-head full-body [])
            prog' (reduce #(prog/assert-rule %2 %1) prog rules)]
        [inner-head prog'])
      ;; Body-only vars: wrap in forall
      (let [innermost-head inner-head
            forall-goal    (define-forall innermost-head bvars)
            outer-inner-head (term/make-compound inner-name prep-args-v)
            wrapper-rule   (prog/make-rule outer-inner-head [forall-goal])
            rules          (comp-dual3 innermost-head full-body [])
            prog'          (reduce #(prog/assert-rule %2 %1)
                                   (prog/assert-rule wrapper-rule prog)
                                   rules)]
        [outer-inner-head prog']))))

;;; ── Outer dual for one predicate ─────────────────────────────────────────────

(defn comp-dual
  "Generate all dual rules for a predicate.  Returns updated program."
  [functor rules prog]
  (if (empty? rules)
    ;; No rules → not_p is a fact
    (prog/assert-rule
     (prog/make-rule
      (outer-dual-head (term/make-compound (term/functor-name-str functor)
                                           (prog/var-list (term/functor-arity functor))))
      [])
     prog)
    (let [dh (outer-dual-head (term/make-compound (term/functor-name-str functor)
                                                   (prog/var-list (term/functor-arity functor))))]
      ;; For each original rule, generate an inner dual
      (let [[inner-goals prog']
            (reduce (fn [[goals p] [clause idx]]
                      (let [[inner-head p'] (comp-dual-for-clause dh clause idx p)]
                        [(conj goals (assoc inner-head :args (:args dh))) p']))
                    [[] prog]
                    (map-indexed (fn [i r] [r (inc i)]) rules))]
        ;; Assert outer dual: not_p(A…) :- inner_1(A…), inner_2(A…), …
        (prog/assert-rule (prog/make-rule dh inner-goals) prog')))))

;;; ── Predicate references in bodies ───────────────────────────────────────────

(defn goal-predicate-functors
  "Collect the user-predicate functor strings *called* within goal g, recursing
   through not/forall/findall wrappers.  Arithmetic/comparison builtins, call/N
   and structurally non-predicate goals contribute nothing.  Conservative: a
   functor it fails to collect simply doesn't get a generated dual (no
   regression, just no extra dual)."
  [g]
  (cond
    (not (term/is-compound? g))          #{}
    (term/is-naf? g)                     (goal-predicate-functors (first (:args g)))
    (term/is-forall? g)                  (goal-predicate-functors (second (:args g)))
    (and (= (:op g) :findall)
         (= 3 (count (:args g))))        (goal-predicate-functors (second (:args g)))
    (term/is-expr? g)                    #{}
    (= (:op g) :call)                    #{}
    (term/is-sneg? g)                    #{}
    :else                                #{(term/term-functor g)}))

(defn- called-functors
  "All user-predicate functors referenced in any rule body or the query."
  [prog]
  (reduce-kv
   (fn [acc _ rules]
     (reduce (fn [a {:keys [body]}]
               (reduce (fn [a2 goal] (into a2 (goal-predicate-functors goal))) a body))
             acc rules))
   (reduce (fn [a goal] (into a (goal-predicate-functors goal)))
           #{} (prog/defined-query prog))
   (:rules prog)))

;;; ── compile-duals entry point ────────────────────────────────────────────────

(defn compile-duals
  "Add dual rules for every user predicate in prog.  Returns updated program.

   Covers both predicates with rules (head functors) AND predicates that are
   only *called* but never defined: an undefined predicate q never holds, so its
   dual not_q must hold universally.  comp-dual with an empty rule list already
   produces exactly that (not_q as a fact), so we simply feed the called-but-
   undefined functors through the same path.  Without this, `not q(X)` for an
   undefined q would have no dual to resolve and wrongly fail."
  [prog]
  (let [head-preds (prog/defined-predicates prog)
        all-preds  (into head-preds (called-functors prog))]
    (reduce (fn [p f]
              (if (or (prog/scasp-builtin? f)
                      (prog/headless-functor? f)
                      (term/is-dual? f))
                p
                (comp-dual f (prog/defined-rules f p) p)))
            prog
            all-preds)))
