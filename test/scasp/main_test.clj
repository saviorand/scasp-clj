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

;;; ── Integrity constraints ────────────────────────────────────────────────────

(deftest integrity-constraint-test
  ;; Program:  a(1). a(2). a(3).
  ;;           :- a(1), a(2).   -- ground constraint: 1 and 2 cannot both hold
  ;;           (this constraint always fires, so NO answer should be produced)
  ;; ?- a(X).
  ;; Without the constraint: 3 answers (X=1, X=2, X=3).
  ;; With    the constraint: 0 answers (constraint body has no variables, so
  ;;   the dual has no forall; it directly checks not_a(1) or a(1),not_a(2),
  ;;   both fail since a(1) and a(2) are facts, so not__chk_0_1 fails = constraint fires).
  (let [false-head {:op :_false :args []}
        rules [(r (c :a 1))
               (r (c :a 2))
               (r (c :a 3))
               {:head false-head :body [(c :a 1) (c :a 2)]}]
        ;; Without constraint: 3 results
        results-no-c (main/solve-all [(r (c :a 1)) (r (c :a 2)) (r (c :a 3))]
                                     [(c :a "X")])
        ;; With constraint: 0 results (constraint always fires)
        results-with-c (main/solve-all rules [(c :a "X")])]
    (is (= 3 (count results-no-c)))
    (is (= 0 (count results-with-c)))))

;;; ── Even-loop variable substitution (Phase 12b) ─────────────────────────────

(deftest even-loop-var-substitution-test
  ;; Classic even loop with a variable:
  ;;   p(X) :- not q(X).
  ;;   q(X) :- not p(X).
  ;;   color(red). color(blue).
  ;;   ?- p(X), color(X).
  ;;
  ;; p(X) calls not q(X), which calls q's dual (not_q(X)), which has
  ;; not p(X) in its body — that detects an even loop back to p(X).
  ;; Coinductive success fires for p(X). Then color(X) binds X to each color.
  ;; With correct var substitution, each branch gets its own frozen X in the
  ;; CHS, so both answers (X=red, X=blue) are produced independently.
  (let [rules [(r (c :p "X") (naf (c :q "X")))
               (r (c :q "X") (naf (c :p "X")))
               (r (c :color :red))
               (r (c :color :blue))]
        results (main/solve-all rules [(c :p "X") (c :color "X")])
        x-vals  (set (map #(vars/var-value "X" (:var-env %)) results))]
    (is (= 2 (count results)))
    (is (contains? x-vals {:val :red}))
    (is (contains? x-vals {:val :blue}))))

;;; ── solve-n — result-count limiting ─────────────────────────────────────────

(deftest solve-n-test
  ;; Three facts: color(red), color(green), color(blue).
  ;; solve-all returns 3; solve-n 2 returns at most 2.
  (let [rules [(r (c :color :red))
               (r (c :color :green))
               (r (c :color :blue))]]
    (is (= 3 (count (main/solve-all rules [(c :color "C")]))))
    (is (= 2 (count (vec (main/solve-n 2 rules [(c :color "C")])))))))

;;; ── DCC: integrity constraints with variables (graph-coloring style) ─────────

(deftest dcc-variable-constraint-test
  ;; node(a). node(b). color(red). color(blue).
  ;; col(X, C) :- node(X), color(C), not diff_col(X, C).
  ;; diff_col(a, blue).
  ;; :- col(X, C), col(Y, C), edge(X, Y).   % constraint with vars
  ;; edge(a, b).
  ;; ?- col(a, C).
  ;; Without constraint: col(a, red) and col(a, blue) are both candidates
  ;; diff_col(a, blue) rules out col(a, blue), so only col(a, red) survives.
  ;; The edge constraint (a,b share no common color) eliminates col(a,C)
  ;; if col(b,C) also holds for the same C.
  ;; col(b, red) holds (no diff_col for b), col(b, blue) holds.
  ;; edge(a,b) exists, so any color shared by a and b fires the constraint.
  ;; col(a, red) + col(b, red) + edge(a,b) → constraint fires → no answers.
  (let [false-head {:op :_false :args []}
        rules [(r (c :node :a))
               (r (c :node :b))
               (r (c :color :red))
               (r (c :color :blue))
               (r (c :col "X" "C") (c :node "X") (c :color "C") (naf (c :diff_col "X" "C")))
               (r (c :diff_col :a :blue))
               (r (c :edge :a :b))
               {:head false-head :body [(c :col "X" "C") (c :col "Y" "C") (c :edge "X" "Y")]}]
        results (main/solve-all rules [(c :col "X" "C")])]
    (is (= 0 (count results)))))

;;; ── Abducible support ────────────────────────────────────────────────────────

(deftest abducible-test
  ;; #abducible fly/1
  ;; bird(tweety).
  ;; ?- fly(tweety).   % abduced: fly(tweety) assumed true with no rules
  (let [rules [(r (c :bird :tweety))]
        results (main/solve-all rules [(c :fly :tweety)] #{"fly/1"})]
    (is (= 1 (count results))))
  ;; With a constraint that fires: fly(X) if bird(X) but not penguin(X).
  ;; penguin(sam).
  ;; :- fly(sam).
  ;; fly(sam) is abducible but the constraint rules it out.
  (let [false-head {:op :_false :args []}
        rules [(r (c :bird :tweety))
               (r (c :penguin :sam))
               {:head false-head :body [(c :fly :sam)]}]
        res-tweety (main/solve-all rules [(c :fly :tweety)] #{"fly/1"})
        res-sam    (main/solve-all rules [(c :fly :sam)]    #{"fly/1"})]
    (is (= 1 (count res-tweety)))
    (is (= 0 (count res-sam)))))

;;; ── solve-forall vacuous truth ───────────────────────────────────────────────

(deftest forall-vacuous-truth-test
  ;; forall(X, impossible(X)) should succeed when impossible/1 has no facts.
  ;; In dual form this appears as a generated forall in the dual of a rule.
  ;; We test it directly via a program that would expose vacuous forall:
  ;;   p :- forall(X, q(X)).
  ;;   (no q facts)
  ;;   ?- p.   % should succeed vacuously
  (let [rules [(r (c :p) {:op :forall :args ["X" (c :q "X")]})]
        results (main/solve-all rules [(c :p)])]
    (is (seq results))))

;;; ── match-neg constraint propagation ────────────────────────────────────────

(deftest match-neg-propagation-test
  ;; p(X) :- not q(X).
  ;; q(a).
  ;; ?- p(X).
  ;; not_q(X) fires: q(a) in CHS makes not_q(a) fail. p(a) fails.
  ;; p(X) where X≠a should coinductively succeed with constraint X≠a propagated.
  ;; We check that p(a) does not appear in answers and that an answer exists.
  (let [rules [(r (c :p "X") (naf (c :q "X")))
               (r (c :q :a))]
        results (main/solve-all rules [(c :p "X")])
        x-vals  (map #(vars/var-value "X" (:var-env %)) results)]
    ;; At least one answer
    (is (seq results))
    ;; No answer has X=a
    (is (not (some #(= {:val :a} %) x-vals)))))
