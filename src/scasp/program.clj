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

;;; ── Construction ─────────────────────────────────────────────────────────────

(defn new-program []
  {:rules {} :query [] :predicates #{} :nmr-check [] :abducibles #{}})

;;; ── Functor helpers ──────────────────────────────────────────────────────────

(defn goal-functor
  "Return the functor string for a goal (compound or NAF-wrapped compound)."
  [goal]
  (cond
    (term/is-naf? goal)
    (let [inner (first (:args goal))]
      (term/negate-functor (term/term-functor inner)))
    (term/is-compound? goal)
    (term/term-functor goal)
    :else nil))

(defn predicate-of
  "Return the positive functor string for a goal (stripping not if NAF)."
  [goal]
  (if (term/is-naf? goal)
    (term/term-functor (first (:args goal)))
    (term/term-functor goal)))

;;; ── Rule operations ──────────────────────────────────────────────────────────

(defn make-rule
  "Create a rule map."
  [head body]
  {:head head :body (vec body)})

(defn assert-rule
  "Add a rule to the program, indexed by head functor."
  [rule prog]
  (let [f (term/term-functor (:head rule))]
    (-> prog
        (update-in [:rules f] (fnil conj []) rule)
        (update :predicates conj f))))

(defn retract-rule
  "Remove first rule matching pred from the program."
  [pred prog]
  (update-in prog [:rules pred] (fn [rs] (vec (rest rs)))))

(defn defined-rules
  "Return all rules for functor-str, or []."
  [functor-str prog]
  (get (:rules prog) functor-str []))

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
  #{"true/0" "false/0" "call/1" "findall/3" "!/0"
    "_false/0" "_nmr_check/0"})

(defn scasp-builtin?
  "True if functor is a built-in that should not have duals generated."
  [f]
  (contains? scasp-builtins f))

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
