(ns scasp.main
  "Programmatic API for scasp-clj.

   Build programs from Clojure data, run queries, inspect results.
   No parser — programs are constructed directly as Clojure maps.

   Term representation:
     Atoms:     keywords   :foo
     Variables: strings    \"X\", \"_\"
     Compounds: maps       {:op :bird :args [:tweety]}
     NAF:       maps       {:op :not  :args [inner-goal]}
     Numbers:   Clojure    42, 3.14

   Quick start:
     (def rules [(prog/make-rule {:op :bird :args [:tweety]} [])
                 (prog/make-rule {:op :flies :args [\"X\"]}
                                 [{:op :bird :args [\"X\"]}
                                  {:op :not  :args [{:op :ab :args [\"X\"]}]}])])
     (solve-all rules [{:op :flies :args [\"X\"]}])"
  (:require [scasp.duals   :as duals]
            [scasp.nmr     :as nmr]
            [scasp.solver  :as solver]
            [scasp.output  :as output]
            [scasp.program :as prog]
            [scasp.vars    :as vars]
            [clojure.string :as str]))

;;; ── Program printing ─────────────────────────────────────────────────────────

(defn print-program
  "Print a compiled program to stdout (useful for debugging dual/NMR output)."
  [program]
  (println "\n;; === Compiled Program ===")
  (doseq [[f rules] (:rules program)]
    (doseq [{:keys [head body]} rules]
      (if (empty? body)
        (println (str (output/fmt-term head (vars/new-var-env)) "."))
        (println (str (output/fmt-term head (vars/new-var-env))
                      " :-\n    "
                      (str/join ",\n    "
                                (map #(output/fmt-term % (vars/new-var-env)) body))
                      "."))))))

;;; ── Programmatic API ─────────────────────────────────────────────────────────

(defn build-program
  "Build a compiled program from Clojure data structures.
   rules:      seq of {:head <term> :body [<goal>...]} maps (use prog/make-rule)
   query:      seq of goal terms
   abducibles: optional set of functor strings (e.g. #{\"fly/1\"})
   Returns a program map ready for solve/run-query."
  ([rules query] (build-program rules query #{}))
  ([rules query abducibles]
   (let [p0 (reduce (fn [p rule] (prog/assert-rule rule p))
                    (prog/new-program)
                    rules)
         p1 (prog/set-query query p0)
         p2 (reduce prog/mark-abducible p1 abducibles)]
     (-> p2 duals/compile-duals nmr/generate-nmr-check))))

(defn solve
  "Solve a query against a set of rules.
   rules:      seq of {:head <term> :body [<goal>...]} maps
   query:      seq of goal terms
   abducibles: optional set of functor strings
   Returns a lazy seq of result maps {:var-env :chs :just :even-loops}."
  ([rules query] (solver/run-query (build-program rules query)))
  ([rules query abducibles] (solver/run-query (build-program rules query abducibles))))

(defn solve-n
  "Return up to n answer sets as a lazy seq."
  [n rules query]
  (take n (solve rules query)))

(defn solve-all
  "Return all answer sets as a vector.
   Warning: may not terminate for programs with infinitely many answer sets."
  ([rules query] (into [] (solve rules query)))
  ([rules query abducibles] (into [] (solve rules query abducibles))))

;;; ── Result helpers ───────────────────────────────────────────────────────────

(defn result-bindings
  "Extract variable bindings from a result map.
   var-names: seq of query variable name strings (e.g. [\"X\" \"Y\"])
   Returns a map {\"X\" <value>, \"Y\" <value>} with values filled in."
  [result var-names]
  (let [ve (:var-env result)]
    (into {} (map (fn [v] [v (vars/fill-in v ve)]) var-names))))

(defn print-results
  "Print answer sets to stdout. query-goals used to extract variable names."
  [results query-goals]
  (if (seq results)
    (doseq [[idx r] (map-indexed #(vector (inc %1) %2) results)]
      (output/print-answer idx r query-goals {}))
    (println "false.")))
