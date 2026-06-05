(ns scasp.builtins-test
  "Tests for findall/3, call/1, true/0, fail/0, var-var CLP(R),
   dual negation of CLP(R) ops, and is/2 RHS deferral."
  (:require [clojure.test :refer [deftest is]]
            [scasp.solver  :as solver]
            [scasp.duals   :as duals]
            [scasp.nmr     :as nmr]
            [scasp.program :as prog]
            [scasp.vars    :as vars]
            [scasp.term    :as term]))

;;; ── Helpers ──────────────────────────────────────────────────────────────────

(defn- c [op & args] {:op op :args (vec args)})
(defn- r [head & body] (prog/make-rule head (vec body)))

(defn- build [rules query]
  (let [p0 (reduce #(prog/assert-rule %2 %1) (prog/new-program) rules)
        p1 (prog/set-query query p0)]
    (-> p1 duals/compile-duals nmr/generate-nmr-check)))

(defn- run [rules query]
  (take 10 (solver/run-query (build rules query))))

(defn- run-goals [goals]
  (run [] goals))

;;; ── true/0 and fail/0 ────────────────────────────────────────────────────────

(deftest true-succeeds-test
  (is (seq (run-goals [(c :true)]))))

(deftest fail-fails-test
  (is (empty? (run-goals [(c :fail)]))))

(deftest false-fails-test
  (is (empty? (run-goals [(c :false)]))))

;;; ── call/1 ───────────────────────────────────────────────────────────────────

(deftest call-direct-test
  ;; call(true) succeeds
  (is (seq (run-goals [(c :call (c :true))]))))

(deftest call-predicate-test
  ;; color(red). ?- call(color(X)).
  (let [results (run [(r (c :color :red))] [(c :call (c :color "X"))])]
    (is (seq results))
    (is (= {:val :red} (vars/var-value "X" (:var-env (first results)))))))

(deftest call-extra-arg-test
  ;; member(X,L) via call(member,X,[a,b])
  (let [list-ab {:op :cons :args [:a {:op :cons :args [:b (keyword "[]")]}]}
        rules [(r (c :member "X" (c :cons "X" "_")))
               (r (c :member "X" (c :cons "_" "T")) (c :member "X" "T"))]
        results (run rules [(c :call (c :member "X") list-ab)])]
    (is (= 2 (count results)))))

;;; ── findall/3 ────────────────────────────────────────────────────────────────

(deftest findall-basic-test
  ;; color(red). color(green). color(blue).
  ;; ?- findall(X, color(X), Bag).
  (let [results (run [(r (c :color :red)) (r (c :color :green)) (r (c :color :blue))]
                     [(c :findall "X" (c :color "X") "Bag")])]
    (is (seq results))
    (let [ve  (:var-env (first results))
          bag (vars/fill-in "Bag" ve)]
      ;; Bag should be a list of 3 elements
      (is (= :cons (:op bag)))
      (let [items (loop [t bag acc []]
                    (if (= t (keyword "[]"))
                      acc
                      (recur (second (:args t)) (conj acc (first (:args t))))))]
        (is (= 3 (count items)))
        (is (= #{:red :green :blue} (set items)))))))

(deftest findall-no-solutions-test
  ;; ?- findall(X, color(X), Bag).  with no color facts → Bag = []
  (let [results (run-goals [(c :findall "X" (c :color "X") "Bag")])]
    (is (seq results))
    (let [ve  (:var-env (first results))
          bag (vars/fill-in "Bag" ve)]
      (is (= (keyword "[]") bag)))))

(deftest findall-with-template-test
  ;; num(1). num(2). num(3).
  ;; ?- findall(f(X), num(X), Bag).
  (let [results (run [(r (c :num 1)) (r (c :num 2)) (r (c :num 3))]
                     [(c :findall (c :f "X") (c :num "X") "Bag")])]
    (is (seq results))
    (let [ve   (:var-env (first results))
          bag  (vars/fill-in "Bag" ve)
          items (loop [t bag acc []]
                  (if (= t (keyword "[]"))
                    acc
                    (recur (second (:args t)) (conj acc (first (:args t))))))]
      (is (= 3 (count items)))
      (is (every? #(= :f (:op %)) items)))))

;;; ── Dual negation of CLP(R) operators ───────────────────────────────────────

(deftest dual-clp-lt-flipped-test
  ;; dual of (.<.) is (.>=.)
  (let [goal (c :clp< "X" "Y")]
    (is (= :clp>= (:op (duals/dual-goal goal))))))

(deftest dual-clp-gt-flipped-test
  (is (= :clp=< (:op (duals/dual-goal (c :clp> "X" "Y"))))))

(deftest dual-clp-le-flipped-test
  (is (= :clp> (:op (duals/dual-goal (c :clp=< "X" "Y"))))))

(deftest dual-clp-ge-flipped-test
  (is (= :clp< (:op (duals/dual-goal (c :clp>= "X" "Y"))))))

(deftest dual-clp-eq-flipped-test
  (is (= :clp<> (:op (duals/dual-goal (c :clp= "X" "Y"))))))

(deftest dual-clp-ne-flipped-test
  (is (= :clp= (:op (duals/dual-goal (c :clp<> "X" "Y"))))))

(deftest dual-hash-ops-test
  (is (= :hash>= (:op (duals/dual-goal (c :hash< "X" "Y")))))
  (is (= :hash=< (:op (duals/dual-goal (c :hash> "X" "Y")))))
  (is (= :hash<> (:op (duals/dual-goal (c :hash= "X" "Y")))))
  (is (= :hash= (:op (duals/dual-goal (c :hash<> "X" "Y"))))))

;;; ── Var-var CLP(R) constraint propagation ────────────────────────────────────

(deftest var-var-constraint-records-test
  ;; X > Y (both unbound) → X gets a relational constraint referencing Y
  (let [results (run-goals [(c :> "X" "Y")])]
    (is (seq results))
    (let [ve (:var-env (first results))
          vc (:var-constraints (vars/var-value "X" ve))]
      (is (seq vc))
      (is (= :> (:op (first vc))))
      (is (= "Y" (:rhs (first vc)))))))

(deftest var-var-propagate-when-rhs-bound-test
  ;; X > Y, Y is 3 → X gets numeric bound lo=3 open
  (let [results (run-goals [(c :> "X" "Y") (c :is "Y" 3)])]
    (is (seq results))
    (let [ve (:var-env (first results))
          b  (get-in (vars/var-value "X" ve) [:numeric-bounds])]
      (is (= 3 (:lo b)))
      (is (true? (:lo-open? b))))))

(deftest var-var-propagate-when-lhs-bound-test
  ;; X > Y, X is 5 → Y gets numeric bound hi=5 open
  (let [results (run-goals [(c :> "X" "Y") (c :is "X" 5)])]
    (is (seq results))
    (let [ve (:var-env (first results))
          b  (get-in (vars/var-value "Y" ve) [:numeric-bounds])]
      (is (= 5 (:hi b)))
      (is (true? (:hi-open? b))))))

(deftest var-var-fails-when-both-bound-incompatible-test
  ;; X > Y, X is 3, Y is 5 → fails (3 > 5 is false)
  (let [results (run-goals [(c :> "X" "Y") (c :is "X" 3) (c :is "Y" 5)])]
    (is (empty? results))))

(deftest var-var-succeeds-when-both-bound-compatible-test
  ;; X > Y, X is 5, Y is 3 → succeeds
  (let [results (run-goals [(c :> "X" "Y") (c :is "X" 5) (c :is "Y" 3)])]
    (is (seq results))))

;;; ── is/2 with unbound RHS ────────────────────────────────────────────────────

(deftest is-defers-unbound-rhs-test
  ;; X is Y (Y unbound) → records X =:= Y, both remain constrained
  (let [results (run-goals [(c :is "X" "Y")])]
    ;; Should succeed (deferred) rather than failing
    (is (seq results))))

(deftest is-defers-then-binds-test
  ;; X is Y, Y is 7 → X = 7
  (let [results (run-goals [(c :is "X" "Y") (c :is "Y" 7)])]
    (is (seq results))
    (is (= 7 (get (vars/var-value "X" (:var-env (first results))) :val)))))

;;; ── CLP(R) in rule bodies with dual propagation ──────────────────────────────

(deftest clp-in-rule-dual-test
  ;; p(X) :- X .<. 10.
  ;; ?- not p(X), X is 5. → fails (5 < 10 so p(5) holds, not p(5) fails)
  ;; ?- not p(X), X is 15. → succeeds (15 >= 10 so p(15) fails, not p(15) succeeds)
  (let [rules [(r (c :p "X") (c :clp< "X" 10))]
        r1 (run rules [(c :not (c :p "X")) (c :is "X" 5)])
        r2 (run rules [(c :not (c :p "X")) (c :is "X" 15)])]
    (is (empty? r1))
    (is (seq r2))))
