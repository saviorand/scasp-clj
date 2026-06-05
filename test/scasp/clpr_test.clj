(ns scasp.clpr-test
  "Tests for CLP(R) symbolic numeric constraint solving."
  (:require [clojure.test :refer [deftest is]]
            [scasp.solver :as solver]
            [scasp.vars   :as vars]
            [scasp.output :as output]
            [scasp.duals  :as duals]
            [scasp.nmr    :as nmr]
            [scasp.program :as prog]))

;;; ── Helpers ──────────────────────────────────────────────────────────────────

(defn- c [op & args] {:op op :args (vec args)})

(defn- run-query-goals
  "Run goals directly as a query (no rules), return all results."
  [goals]
  (let [p0 (prog/set-query goals (prog/new-program))
        p1 (-> p0 duals/compile-duals nmr/generate-nmr-check)]
    (take 5 (solver/run-query p1))))

(defn- var-bounds [varname ve]
  (get-in (vars/var-value varname ve) [:numeric-bounds]))

(defn- var-val [varname ve]
  (get (vars/var-value varname ve) :val))

;;; ── Single constraint, X unbound ────────────────────────────────────────────

(deftest symbolic-gt-test
  ;; ?- X > 0.  → X unbound, lo = 0 (open)
  (let [results (run-query-goals [(c :> "X" 0)])]
    (is (seq results))
    (let [ve (:var-env (first results))
          b  (var-bounds "X" ve)]
      (is (= 0 (:lo b)))
      (is (true? (:lo-open? b))))))

(deftest symbolic-lt-test
  ;; ?- X < 10.  → X unbound, hi = 10 (open)
  (let [results (run-query-goals [(c :< "X" 10)])]
    (is (seq results))
    (let [ve (:var-env (first results))
          b  (var-bounds "X" ve)]
      (is (= 10 (:hi b)))
      (is (true? (:hi-open? b))))))

(deftest symbolic-ge-test
  ;; ?- X >= 3.  → lo = 3 (closed)
  (let [results (run-query-goals [(c :>= "X" 3)])]
    (is (seq results))
    (let [ve (:var-env (first results))
          b  (var-bounds "X" ve)]
      (is (= 3 (:lo b)))
      (is (false? (:lo-open? b))))))

(deftest symbolic-le-test
  ;; ?- X =< 7.  → hi = 7 (closed)
  (let [results (run-query-goals [(c :=< "X" 7)])]
    (is (seq results))
    (let [ve (:var-env (first results))
          b  (var-bounds "X" ve)]
      (is (= 7 (:hi b)))
      (is (false? (:hi-open? b))))))

;;; ── Interval intersection ────────────────────────────────────────────────────

(deftest interval-intersection-test
  ;; ?- X > 0, X < 10.  → X∈(0,10)
  (let [results (run-query-goals [(c :> "X" 0) (c :< "X" 10)])]
    (is (seq results))
    (let [ve (:var-env (first results))
          b  (var-bounds "X" ve)]
      (is (= 0 (:lo b)))
      (is (= 10 (:hi b)))
      (is (true? (:lo-open? b)))
      (is (true? (:hi-open? b))))))

(deftest interval-tighten-test
  ;; ?- X > 0, X < 10, X > 5.  → X∈(5,10)
  (let [results (run-query-goals [(c :> "X" 0) (c :< "X" 10) (c :> "X" 5)])]
    (is (seq results))
    (let [ve (:var-env (first results))
          b  (var-bounds "X" ve)]
      (is (= 5 (:lo b)))
      (is (= 10 (:hi b))))))

;;; ── Empty interval → failure ─────────────────────────────────────────────────

(deftest empty-interval-fails-test
  ;; ?- X > 0, X < 0.  → fails
  (let [results (run-query-goals [(c :> "X" 0) (c :< "X" 0)])]
    (is (empty? results))))

(deftest empty-interval-same-point-strict-fails-test
  ;; ?- X > 5, X < 5.  → fails
  (let [results (run-query-goals [(c :> "X" 5) (c :< "X" 5)])]
    (is (empty? results))))

;;; ── Constraint then bind ─────────────────────────────────────────────────────

(deftest constraint-then-bind-success-test
  ;; ?- X > 3, X is 5.  → succeeds, X=5
  (let [results (run-query-goals [(c :> "X" 3) (c :is "X" 5)])]
    (is (seq results))
    (is (= 5 (var-val "X" (:var-env (first results)))))))

(deftest constraint-then-bind-fail-test
  ;; ?- X > 3, X is 2.  → fails (2 violates X>3)
  (let [results (run-query-goals [(c :> "X" 3) (c :is "X" 2)])]
    (is (empty? results))))

(deftest bind-then-constraint-success-test
  ;; ?- X is 5, X > 3.  → succeeds, X=5
  (let [results (run-query-goals [(c :is "X" 5) (c :> "X" 3)])]
    (is (seq results))
    (is (= 5 (var-val "X" (:var-env (first results)))))))

(deftest bind-then-constraint-fail-test
  ;; ?- X is 2, X > 3.  → fails
  (let [results (run-query-goals [(c :is "X" 2) (c :> "X" 3)])]
    (is (empty? results))))

;;; ── Equality constraint binds ────────────────────────────────────────────────

(deftest clp-eq-binds-test
  ;; ?- X =:= 7.  → X bound to 7
  (let [results (run-query-goals [(c :=:= "X" 7)])]
    (is (seq results))
    (is (= 7 (var-val "X" (:var-env (first results)))))))

;;; ── Numeric disequality ──────────────────────────────────────────────────────

(deftest arith-ne-records-test
  ;; ?- X =\= 3.  → X unbound with numeric-neq #{3}
  (let [results (run-query-goals [(c :arith-ne "X" 3)])]
    (is (seq results))
    (let [ve (:var-env (first results))]
      (is (contains? (:numeric-neq (vars/var-value "X" ve)) 3)))))

(deftest arith-ne-blocks-bind-test
  ;; ?- X =\= 3, X is 3.  → fails
  (let [results (run-query-goals [(c :arith-ne "X" 3) (c :is "X" 3)])]
    (is (empty? results))))

(deftest arith-ne-allows-other-bind-test
  ;; ?- X =\= 3, X is 4.  → succeeds
  (let [results (run-query-goals [(c :arith-ne "X" 3) (c :is "X" 4)])]
    (is (seq results))
    (is (= 4 (var-val "X" (:var-env (first results)))))))

;;; ── CLP(R) symbolic operators (:clp< etc.) ───────────────────────────────────

(deftest clp-dot-ops-test
  ;; ?- X .<. 10, X .>. 2.  → X∈(2,10)
  (let [results (run-query-goals [(c :clp< "X" 10) (c :clp> "X" 2)])]
    (is (seq results))
    (let [ve (:var-env (first results))
          b  (var-bounds "X" ve)]
      (is (= 2 (:lo b)))
      (is (= 10 (:hi b))))))

(deftest clp-hash-ops-test
  ;; ?- X #< 10, X #> 2.  → X∈(2,10)
  (let [results (run-query-goals [(c :hash< "X" 10) (c :hash> "X" 2)])]
    (is (seq results))
    (let [ve (:var-env (first results))
          b  (var-bounds "X" ve)]
      (is (= 2 (:lo b)))
      (is (= 10 (:hi b))))))

;;; ── Output formatting ────────────────────────────────────────────────────────

(deftest fmt-constrained-var-test
  ;; After X > 0, X < 10: fmt-term should mention the bounds
  (let [results (run-query-goals [(c :> "X" 0) (c :< "X" 10)])]
    (is (seq results))
    (let [ve  (:var-env (first results))
          out (output/fmt-term "X" ve)]
      (is (string? out))
      (is (re-find #"0" out))
      (is (re-find #"10" out)))))

(deftest fmt-free-var-test
  ;; Unconstrained X prints as "X"
  (let [ve (vars/new-var-env)]
    (is (= "X" (output/fmt-term "X" ve)))))
