(ns scasp.solver-test
  "Integration tests for the s(CASP) solver engine.
   Programs are built directly as Clojure data — no string parser needed."
  (:require [clojure.test  :refer [deftest is]]
            [scasp.solver  :as solver]
            [scasp.duals   :as duals]
            [scasp.nmr     :as nmr]
            [scasp.program :as prog]
            [scasp.vars    :as vars]))

;;; ── Helpers ──────────────────────────────────────────────────────────────────

(defn- c
  "Shorthand for a compound term."
  [op & args]
  {:op op :args (vec args)})

(defn- r
  "Shorthand for a rule."
  [head & body]
  (prog/make-rule head (vec body)))

(defn- build-program
  "Assemble a program from rules and a query, then compile duals + NMR check."
  [rules query]
  (let [p0 (reduce (fn [p rule] (prog/assert-rule rule p))
                   (prog/new-program)
                   rules)
        p1 (prog/set-query query p0)]
    (-> p1 duals/compile-duals nmr/generate-nmr-check)))

(defn- run-program
  "Build and run a program, returning up to n results."
  ([rules query] (run-program rules query 10))
  ([rules query n]
   (take n (solver/run-query (build-program rules query)))))

;;; ── Simple fact + query ──────────────────────────────────────────────────────

(deftest fact-query-test
  ;; bird(tweety).  ?- bird(X).
  (let [results (run-program [(r (c :bird :tweety))]
                             [(c :bird "X")]
                             5)]
    (is (seq results))
    (is (= {:val :tweety} (vars/var-value "X" (:var-env (first results)))))))

;;; ── NAF: flies if bird and not abnormal ──────────────────────────────────────

(deftest bird-test
  ;; flies(X) :- bird(X), not ab(X).
  ;; ab(X)    :- penguin(X).
  ;; bird(X)  :- penguin(X).
  ;; bird(tweety). bird(sam). penguin(tweety).
  ;; ?- flies(X).
  (let [rules [(r (c :flies "X")   (c :bird "X") {:op :not :args [(c :ab "X")]})
               (r (c :ab "X")      (c :penguin "X"))
               (r (c :bird "X")    (c :penguin "X"))
               (r (c :bird :tweety))
               (r (c :bird :sam))
               (r (c :penguin :tweety))]
        results (run-program rules [(c :flies "X")] 5)]
    (is (seq results))
    (is (some (fn [r] (= {:val :sam} (vars/var-value "X" (:var-env r)))) results))))

;;; ── Arithmetic ────────────────────────────────────────────────────────────────

(deftest arithmetic-test
  ;; ?- X is 2 + 3, X > 4.
  (let [results (run-program []
                             [(c :is "X" (c :+ 2 3)) (c :> "X" 4)]
                             1)]
    (is (seq results))
    (is (= {:val 5} (vars/var-value "X" (:var-env (first results)))))))

;;; ── Disequality ──────────────────────────────────────────────────────────────

(deftest disequality-test
  ;; p(a). p(b). q(X) :- p(X), X \= a.  ?- q(X).
  (let [rules [(r (c :p :a))
               (r (c :p :b))
               (r (c :q "X") (c :p "X") (c :ne "X" :a))]
        results (run-program rules [(c :q "X")] 5)]
    (is (seq results))
    (is (= {:val :b} (vars/var-value "X" (:var-env (first results)))))))

;;; ── Multiple solutions / backtracking ────────────────────────────────────────

(deftest backtracking-test
  ;; color(red). color(green). color(blue).  ?- color(X).
  (let [rules [(r (c :color :red))
               (r (c :color :green))
               (r (c :color :blue))]
        results (run-program rules [(c :color "X")] 10)]
    (is (= 3 (count results)))))

;;; ── Odd loop over negation (self-referential NAF) ────────────────────────────

(deftest olon-test
  ;; p :- not p.    (odd loop — stable model has p absent)
  ;; ?- not p.
  (let [rules [(r (c :p) {:op :not :args [(c :p)]})]
        results (run-program rules [{:op :not :args [(c :p)]}] 5)]
    (is (seq results))))

;;; ── Recursive rules ──────────────────────────────────────────────────────────

(deftest recursive-test
  ;; member(X,[X|_]).
  ;; member(X,[_|T]) :- member(X,T).
  ;; ?- member(X, [a,b,c]).
  (let [list-abc {:op :cons :args [:a {:op :cons :args [:b {:op :cons :args [:c (keyword "[]")]}]}]}
        rules [(r (c :member "X" (c :cons "X" "_"))
                )
               (r (c :member "X" (c :cons "_" "T"))
                  (c :member "X" "T"))]
        results (run-program rules [(c :member "X" list-abc)] 10)]
    (is (= 3 (count results)))))
