(ns scasp.main-test
  "Phase 10 integration tests for the programmatic scasp.main API.
   Programs are built as Clojure data — no string parser needed."
  (:require [clojure.test :refer [deftest is]]
            [scasp.main    :as main]
            [scasp.program :as prog]
            [scasp.vars    :as vars]))

;;; ── Helpers ──────────────────────────────────────────────────────────────────

(defn- c [op & args] {:op op :args (vec args)})
(defn- r [head & body] (prog/make-rule head (vec body)))
(defn- naf [g] {:op :not :args [g]})

;;; ── Tweety — basic default reasoning ────────────────────────────────────────

(deftest tweety-test
  ;; flies(X) :- bird(X), not ab(X).
  ;; ab(X)    :- penguin(X).
  ;; bird(X)  :- penguin(X).
  ;; bird(tweety).
  ;; penguin(sam).
  ;; ?- flies(X).
  ;; Expected: one answer, X = tweety.
  (let [rules [(r (c :flies "X") (c :bird "X") (naf (c :ab "X")))
               (r (c :ab "X") (c :penguin "X"))
               (r (c :bird "X") (c :penguin "X"))
               (r (c :bird :tweety))
               (r (c :penguin :sam))]
        results (main/solve-all rules [(c :flies "X")])]
    (is (= 1 (count results)))
    (is (= {:val :tweety} (vars/var-value "X" (:var-env (first results)))))))

;;; ── Family — recursive rules ─────────────────────────────────────────────────

(deftest family-test
  ;; parent(tom, bob). parent(bob, ann).
  ;; ancestor(X, Y) :- parent(X, Y).
  ;; ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
  ;; ?- ancestor(tom, Y).
  ;; Expected: two answers, Y = bob and Y = ann.
  (let [rules [(r (c :parent :tom :bob))
               (r (c :parent :bob :ann))
               (r (c :ancestor "X" "Y") (c :parent "X" "Y"))
               (r (c :ancestor "X" "Y") (c :parent "X" "Z") (c :ancestor "Z" "Y"))]
        results (main/solve-all rules [(c :ancestor :tom "Y")])
        y-vals  (set (map #(vars/var-value "Y" (:var-env %)) results))]
    (is (= 2 (count results)))
    (is (contains? y-vals {:val :bob}))
    (is (contains? y-vals {:val :ann}))))

;;; ── Self-referential NAF (OLON) via the solve API ───────────────────────────

(deftest olon-api-test
  ;; p :- not p.   (odd loop — stable model has p absent)
  ;; ?- not p.     should succeed
  (let [rules   [(r (c :p) (naf (c :p)))]
        results (main/solve-all rules [(naf (c :p))])]
    (is (seq results))))

;;; ── solve-n — result-count limiting ─────────────────────────────────────────

(deftest solve-n-test
  ;; Three facts: color(red), color(green), color(blue).
  ;; solve-all returns 3; solve-n 2 returns at most 2.
  (let [rules [(r (c :color :red))
               (r (c :color :green))
               (r (c :color :blue))]]
    (is (= 3 (count (main/solve-all rules [(c :color "C")]))))
    (is (= 2 (count (vec (main/solve-n 2 rules [(c :color "C")])))))))
