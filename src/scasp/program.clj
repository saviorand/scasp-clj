(ns scasp.program
  "In-memory program database.

   A program is a map:
     {:rules      {functor-str → [rule …]}
      :query      [goal …]
      :predicates #{functor-str …}
      :nmr-check  [goal …]}

   A rule is a map:
     {:head compound-term
      :body [goal …]}"
  (:require [scasp.term :as term]))

(declare var-list)

;;; ── Construction ─────────────────────────────────────────────────────────────

(defn new-program []
  {:rules {} :query [] :predicates #{} :nmr-check [] :abducibles #{}})

;;; ── Functor helpers ──────────────────────────────────────────────────────────

(defn goal-functor
  "Return the functor string for a goal (compound, NAF-wrapped, or sneg-wrapped)."
  [goal]
  (cond
    (term/is-naf? goal)
    (let [inner (first (:args goal))]
      (term/negate-functor (term/term-functor inner)))
    (term/is-sneg? goal)
    (let [inner (first (:args goal))]
      (term/strong-negate-functor (term/term-functor inner)))
    (term/is-compound? goal)
    (term/term-functor goal)
    :else nil))

(defn predicate-of
  "Return the positive functor string for a goal (stripping not/sneg wrapper)."
  [goal]
  (cond
    (term/is-naf? goal)  (term/term-functor (first (:args goal)))
    (term/is-sneg? goal) (term/strong-negate-functor (term/term-functor (first (:args goal))))
    :else                (term/term-functor goal)))

;;; ── Rule operations ──────────────────────────────────────────────────────────

(defn make-rule
  "Create a rule map."
  [head body]
  {:head head :body (vec body)})

(defn assert-rule
  "Add a rule to the program, indexed by head functor.
   When the head is a strongly-negated predicate (-p/N), automatically
   registers a consistency _false/0 rule (:- p(X), -p(X)) the first time
   any -p/N rule is asserted, ensuring p and -p cannot both hold."
  [rule prog]
  (let [f    (term/term-functor (:head rule))
        prog' (-> prog
                  (update-in [:rules f] (fnil conj []) rule)
                  (update :predicates conj f))]
    (if (and (term/is-strong-neg? f)
             (not (contains? (:strong-neg-constrained prog) f)))
      ;; First rule for -p/N: auto-add the consistency constraint :- p(X…), -p(X…)
      (let [n          (term/functor-arity f)
            pos-name   (term/functor-name-str (term/strong-negate-functor f))
            vars       (var-list n)
            pos-goal   (term/make-compound pos-name vars)
            neg-goal   (term/make-compound (term/functor-name-str f) vars)
            false-head {:op :_false :args []}
            cons-rule  {:head false-head :body [pos-goal neg-goal]}]
        (-> prog'
            (update-in [:rules "_false/0"] (fnil conj []) cons-rule)
            (update :strong-neg-constrained (fnil conj #{}) f)))
      prog')))

(defn retract-rule
  "Remove first rule matching pred from the program."
  [pred prog]
  (update-in prog [:rules pred] (fn [rs] (vec (rest rs)))))

(defn defined-rules
  "Return all rules for functor-str, or []."
  [functor-str prog]
  (get (:rules prog) functor-str []))

;;; ── First-argument clause indexing ───────────────────────────────────────────
;;; Mirrors the WAM first-argument indexing that SWI/Ciao get for free from the
;;; underlying Prolog engine (pr_rule(Goal, …) is indexed on Goal's principal
;;; functor + first arg). Semantics-preserving: we only skip clauses whose head
;;; first-arg can provably never unify with the goal's first arg.

(defn index-key
  "Index key for a (resolved) term's first-argument position.
   A variable matches anything → :var. Constants/compounds get a discriminating key."
  [t]
  (cond
    (term/is-var? t)      :var
    (term/is-compound? t) [:c (:op t) (count (:args t))]
    (keyword? t)          [:a t]
    (number? t)           [:n t]
    :else                 [:o t]))

(defn- head-first-key [rule]
  (let [args (:args (:head rule))]
    (if (empty? args) :nullary (index-key (first args)))))

(defn build-rule-index
  "Precompute a first-argument index per functor. Stored under :rule-index as
     functor → {:all [rule…] :groups {key [[idx rule]…]} :vars [[idx rule]…]}
   :all preserves original clause order; :groups/:vars carry positions so a
   constant lookup can be merged with variable-headed clauses in order."
  [prog]
  (assoc prog :rule-index
         (reduce-kv
          (fn [m f rules]
            (let [indexed (map-indexed (fn [i r] [i (head-first-key r) r]) rules)
                  vars    (filterv (fn [[_ k _]] (= k :var)) indexed)
                  groups  (reduce (fn [g [i k r]]
                                    (if (= k :var) g
                                        (update g k (fnil conj []) [i r])))
                                  {} indexed)]
              (assoc m f {:all   (vec rules)
                          :vars  (mapv (fn [[i _ r]] [i r]) vars)
                          :groups groups})))
          {} (:rules prog))))

(defn candidate-rules
  "Return the clauses for functor that could unify with a goal whose first
   argument has the given index-key (compute via index-key on the resolved arg,
   or :var / :nullary). Falls back to all rules if no index is present."
  [functor goal-key prog]
  (if-let [idx (get (:rule-index prog) functor)]
    (if (or (= goal-key :var) (= goal-key :nullary))
      (:all idx)
      (let [g (get (:groups idx) goal-key)
            v (:vars idx)]
        (cond
          (empty? v) (mapv second (or g []))
          (nil? g)   (mapv second v)
          :else      (mapv second (sort-by first (into (vec g) v))))))
    (defined-rules functor prog)))

(defn defined-predicates
  "Return the set of all predicate functor strings in the program."
  [prog]
  (:predicates prog))

;;; ── Query / NMR ──────────────────────────────────────────────────────────────

(defn set-query [goals prog]
  (assoc prog :query (vec goals)))

(defn defined-query [prog]
  (:query prog))

(defn assert-nmr-check [goals prog]
  (assoc prog :nmr-check (vec goals)))

(defn defined-nmr-check [prog]
  (:nmr-check prog))

;;; ── Predicates on functors ───────────────────────────────────────────────────

(def ^:private scasp-builtins
  #{"true/0" "false/0" "fail/0" "call/1" "call/2" "call/3" "call/4"
    "findall/3" "!/0" "_false/0" "_nmr_check/0"
    "print/1" "println/1" "nl/0" "read_line/1" "read_number/1"
    "string_concat/3" "string_length/2" "atom_string/2"
    "write_file/2" "read_file/2" "append_file/2" "file_exists/1"
    "now_hour/1" "now_minute/1" "now_second/1" "now_timestamp/1" "now_date/1"
    "env_var/2" "random_int/2" "format_number/3" "clj_call/3" "clj_call/4"
    "clj_call/5" "clj_call/6"})

(defn scasp-builtin?
  "True if functor is a built-in that should not have duals generated."
  [f]
  (or (contains? scasp-builtins f)
      (= "findall" (term/functor-name-str f))
      (= "call"    (term/functor-name-str f))))

(defn headless-functor?
  "The dummy functor used for integrity constraints (:- body.)."
  [f]
  (= "_false/0" f))

;;; ── Var-list builder (used by dual compilation) ──────────────────────────────

(defn var-list
  "Build a list of n fresh variable names: [\"_A0\" \"_A1\" …]."
  [n]
  (mapv #(str "_A" %) (range n)))

;;; ── Abducible support ────────────────────────────────────────────────────────

(defn mark-abducible
  "Register functor-str as abducible in the program."
  [prog functor-str]
  (update prog :abducibles conj functor-str))

(defn abducible?
  "True if functor-str is marked as abducible."
  [functor-str prog]
  (contains? (:abducibles prog) functor-str))

;;; ── Create a unique internal functor ────────────────────────────────────────

(defn create-unique-functor
  "Append a counter to a functor name string, keeping arity."
  [base counter]
  (let [n   (term/functor-name-str base)
        ar  (term/functor-arity base)]
    (str n "_" counter "/" ar)))
