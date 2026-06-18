(ns scasp.term
  "Term representation and basic operations.

   Term types:
   - Variables  : strings  \"X\", \"_Foo\", \"_\"
   - Atoms      : keywords :foo, :bar
   - Numbers    : Clojure  42, 3.14, 2/3
   - Compounds  : maps     {:op :foo :args [\"X\" :bar]}
   - NAF goal   : map      {:op :not :args [inner-goal]}
   - Forall     : map      {:op :forall :args [\"V\" goal]}"
  (:require [clojure.string :as str]
            [clojure.set :as set]))

;;; ── Type predicates ──────────────────────────────────────────────────────────

(defn is-var?
  "A term is a variable iff it is a string (first non-_ char is uppercase or it is _)."
  [t]
  (string? t))

(defn is-atom? [t] (keyword? t))
(defn is-number? [t] (number? t))

(defn is-string-val?
  "True if t is a string literal value (not a variable)."
  [t]
  (and (map? t) (contains? t :scasp/string)))

(defn string-val
  "Create a string literal value."
  [s]
  {:scasp/string s})

(defn string-val-str
  "Extract the raw string from a string literal value."
  [t]
  (:scasp/string t))

(defn is-compound?
  "A term is compound iff it is a map with :op and :args."
  [t]
  (and (map? t) (contains? t :op) (contains? t :args)))

(defn is-naf?
  "NAF goal: {:op :not :args [inner]}."
  [t]
  (and (is-compound? t) (= (:op t) :not) (= (count (:args t)) 1)))

(defn is-sneg?
  "Strong negation goal: {:op :sneg :args [inner]}.
   Represents classical/explicit negation -p(X)."
  [t]
  (and (is-compound? t) (= (:op t) :sneg) (= (count (:args t)) 1)))

(defn is-forall?
  "Forall goal: {:op :forall :args [var-string goal]}."
  [t]
  (and (is-compound? t) (= (:op t) :forall) (= (count (:args t)) 2)))

;;; ── Functor helpers ──────────────────────────────────────────────────────────

(defn term-functor
  "Return the functor string 'name/arity' for a compound term."
  [t]
  (str (name (:op t)) "/" (count (:args t))))

(defn functor-name-str
  "'foo/2' → 'foo'"
  [^String f]
  (let [idx (.lastIndexOf f "/")]
    (if (neg? idx) f (subs f 0 idx))))

(defn functor-arity
  "'foo/2' → 2"
  [^String f]
  (let [idx (.lastIndexOf f "/")]
    (if (neg? idx) 0 (Integer/parseInt (subs f (inc idx))))))

(defn make-compound
  "Build a compound from a functor name string and an args vector."
  [name-str args]
  {:op (keyword name-str) :args (vec args)})

(defn compound-op   [t] (:op t))
(defn compound-args [t] (:args t))

;;; ── Functor negation ─────────────────────────────────────────────────────────

(defn negate-functor
  "Flip between positive and negative functor strings.
   'foo/1' ↔ 'not_foo/1'"
  [^String f]
  (let [n   (functor-name-str f)
        ar  (subs f (inc (.lastIndexOf f "/")))]
    (if (str/starts-with? n "not_")
      (str (subs n 4) "/" ar)
      (str "not_" n "/" ar))))

(defn is-dual?
  "True if the functor string starts with 'not_' or '_not_' (inner dual).
   Strong negation '-foo' is NOT a dual — it is a regular predicate."
  [^String f]
  (let [n (functor-name-str f)]
    (or (str/starts-with? n "not_")
        (str/starts-with? n "_not_"))))

(defn is-strong-neg?
  "True if the functor string represents a strongly-negated predicate ('-foo/1')."
  [^String f]
  (str/starts-with? (functor-name-str f) "-"))

(defn strong-negate-functor
  "Flip between positive and strongly-negated functor strings.
   'foo/1' ↔ '-foo/1'"
  [^String f]
  (let [n  (functor-name-str f)
        ar (subs f (inc (.lastIndexOf f "/")))]
    (if (str/starts-with? n "-")
      (str (subs n 1) "/" ar)
      (str "-" n "/" ar))))

(defn reserved-functor?
  "True if the functor's name starts with '_' (internal/reserved)."
  [^String f]
  (str/starts-with? (functor-name-str f) "_"))

;;; ── Variable collection ──────────────────────────────────────────────────────

(defn term-vars
  "Collect all variable strings appearing in t as a set."
  [t]
  (cond
    (is-var? t)        #{t}
    (is-string-val? t) #{}
    (is-compound? t)   (transduce (map term-vars) set/union #{} (:args t))
    :else              #{}))

(defn terms-vars
  "Collect all variables from a list of terms."
  [ts]
  (transduce (map term-vars) set/union #{} ts))

(defn term-vars-list
  "Return a list (with duplicates) of all variable strings in t, in order."
  [t]
  (cond
    (is-var? t)        [t]
    (is-string-val? t) []
    (is-compound? t)   (mapcat term-vars-list (:args t))
    :else              []))

;;; ── Structural substitution ──────────────────────────────────────────────────

(defn substitute
  "Structurally replace every occurrence of var-name with value in term t."
  [var-name value t]
  (cond
    (= t var-name)     value
    (is-string-val? t) t
    (is-compound? t)   (update t :args (fn [args] (mapv #(substitute var-name value %) args)))
    :else              t))

;;; ── Operator / expression predicates ────────────────────────────────────────

;;; Operator keyword naming convention (safe Clojure keywords):
;;;   Prolog \=    → :ne           (disequality / does-not-unify)
;;;   Prolog =\=   → :arith-ne     (arithmetic not-equal)
;;;   Prolog @<    → :term<        (term ordering)
;;;   Prolog @>    → :term>
;;;   Prolog @=<   → :term<=
;;;   Prolog @>=   → :term>=
;;;   Prolog /     → :div          (/ is namespace separator in keywords)
;;;   Prolog //    → :idiv
;;;   Prolog **    → :pow
;;;   Prolog ^     → :hat

(def ^:private comparison-ops
  #{:= :ne :is :=:= :arith-ne :< :> :=< :>= :term< :term> :term<= :term>=
    ;; CLP(R) symbolic comparison operators
    :clp< :clp> :clp=< :clp>= :clp= :clp<>
    ;; CLP(R) #-prefixed aliases
    :hash= :hash< :hash> :hash>= :hash=< :hash<>})

(def ^:private arith-ops
  #{:+ :- :* :div :idiv :rem :mod :<< :>> :pow :hat :abs :max :min :float :integer :sign})

(defn comparison-op?
  "True if term is a comparison expression."
  [t]
  (and (is-compound? t) (contains? comparison-ops (:op t))))

(defn arith-expr?
  "True if term is an arithmetic expression."
  [t]
  (and (is-compound? t) (contains? arith-ops (:op t))))

(defn is-expr?
  "True if this compound term is an arithmetic/comparison expression, not a predicate call."
  [t]
  (or (comparison-op? t)
      (arith-expr? t)
      (and (is-compound? t) (= (:op t) :is))
      (and (is-compound? t) (= (:op t) :not)
           (let [inner (first (:args t))]
             (and (is-compound? inner) (= (:op inner) :is))))))

;;; ── Operator string ↔ keyword mapping ───────────────────────────────────────

(def op-str->kw
  "Map from Prolog operator string to Clojure-safe keyword."
  {"="    :=
   "\\="  :ne
   "is"   :is
   "=:="  :=:=
   "=\\=" :arith-ne
   "<"    :<
   ">"    :>
   "=<"   :=<
   ">="   :>=
   "@<"   :term<
   "@>"   :term>
   "@=<"  :term<=
   "@>="  :term>=
   "+"    :+
   "-"    :-
   "*"    :*
   "/"    :div
   "//"   :idiv
   "rem"  :rem
   "mod"  :mod
   "**"   :pow
   "^"    :hat
   "<<"   :<<
   ">>"   :>>
   "not"  :not
   "\\+"  :not
   ":-"   :rule
   "?-"   :query
   ","    :and
   ";"    :or
   "->"   :->
   ;; CLP(R) s(CASP)-style symbolic operators (.<. .>. etc.)
   ".<."  :clp<
   ".>."  :clp>
   ".=<." :clp=<
   ".>=." :clp>=
   ".=."  :clp=
   ".<>." :clp<>
   ;; CLP(R) #-prefixed aliases
   "#="   :hash=
   "#<"   :hash<
   "#>"   :hash>
   "#>="  :hash>=
   "#=<"  :hash=<
   "#<>"  :hash<>})

(def op-kw->str
  "Reverse map: keyword → Prolog operator string for printing."
  (into {} (map (fn [[k v]] [v k]) op-str->kw)))

;;; ── Pretty-printing utilities ────────────────────────────────────────────────

(declare pp-term)

(defn pp-args [args]
  (str "(" (str/join ", " (map pp-term args)) ")"))

(defn pp-term
  "Return a human-readable string for a term (no var-env lookup)."
  [t]
  (cond
    (is-var? t)        t
    (is-atom? t)       (name t)
    (is-number? t)     (str t)
    (is-string-val? t) (str "\"" (string-val-str t) "\"")
    (is-sneg? t)       (str "-" (pp-term (first (:args t))))
    (is-naf? t)      (str "not " (pp-term (first (:args t))))
    (is-forall? t)   (str "forall(" (pp-term (first (:args t))) ", " (pp-term (second (:args t))) ")")
    (is-compound? t) (str (name (:op t)) (pp-args (:args t)))
    :else            (pr-str t)))
