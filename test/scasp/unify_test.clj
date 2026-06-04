(ns scasp.unify-test
  (:require [clojure.test :refer :all]
            [scasp.vars   :as vars]
            [scasp.unify  :as unify]))

(deftest atom-unify-test
  (let [ve (vars/new-var-env)]
    (is (some? (unify/solve-unify :foo :foo ve false)))
    (is (nil?  (unify/solve-unify :foo :bar ve false)))))

(deftest number-unify-test
  (let [ve (vars/new-var-env)]
    (is (some? (unify/solve-unify 42 42 ve false)))
    (is (nil?  (unify/solve-unify 42 43 ve false)))))

(deftest var-atom-unify-test
  (let [ve  (vars/new-var-env)
        ve' (unify/solve-unify "X" :foo ve false)]
    (is (some? ve'))
    (is (= {:val :foo} (vars/var-value "X" ve')))))

(deftest var-var-unify-test
  (let [ve  (vars/new-var-env)
        ve1 (unify/solve-unify "X" "Y" ve false)]
    (is (some? ve1))
    ;; Binding X should propagate to Y
    (let [ve2 (vars/update-var-value "X" {:val :bar} ve1)]
      (is (= {:val :bar} (vars/var-value "Y" ve2))))))

(deftest compound-unify-test
  (let [ve (vars/new-var-env)
        t1 {:op :f :args ["X" :a]}
        t2 {:op :f :args [:b   :a]}
        ve' (unify/solve-unify t1 t2 ve false)]
    (is (some? ve'))
    (is (= {:val :b} (vars/var-value "X" ve')))))

(deftest compound-arity-mismatch-test
  (let [ve (vars/new-var-env)
        t1 {:op :f :args ["X"]}
        t2 {:op :f :args ["X" :a]}]
    (is (nil? (unify/solve-unify t1 t2 ve false)))))

(deftest constraint-violation-test
  (let [ve  (vars/new-var-env)
        ve' (vars/add-var-constraint "X" :foo ve)]
    ;; Cannot unify X with :foo (constrained against it)
    (is (nil? (unify/solve-unify "X" :foo ve' false)))))

(deftest dnunify-add-constraint-test
  (let [ve  (vars/new-var-env)
        ve' (unify/solve-dnunify "X" :foo ve)]
    (is (some? ve'))
    (is (contains? (:constraints (vars/var-value "X" ve')) :foo))))

(deftest dnunify-atoms-different-test
  (let [ve (vars/new-var-env)]
    (is (some? (unify/solve-dnunify :foo :bar ve)))
    (is (nil?  (unify/solve-dnunify :foo :foo ve)))))
