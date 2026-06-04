(ns scasp.vars-test
  (:require [clojure.test :refer :all]
            [scasp.vars :as vars]))

(deftest new-var-env-test
  (let [ve (vars/new-var-env)]
    (is (empty? (:names ve)))
    (is (empty? (:values ve)))
    (is (zero? (:name-cnt ve)))
    (is (zero? (:id-cnt ve)))))

(deftest update-and-lookup-test
  (let [ve  (vars/new-var-env)
        ve' (vars/update-var-value "X" {:val :foo} ve)]
    (is (= {:val :foo} (vars/var-value "X" ve')))))

(deftest default-unbound-test
  (let [ve (vars/new-var-env)]
    ;; Variable not in env → default unbound struct
    (is (= {:constraints #{} :bindable? true :loop-var 0}
           (vars/var-value "X" ve)))
    (is (vars/is-unbound? "X" ve))))

(deftest bind-and-check-test
  (let [ve (vars/new-var-env)
        ve' (vars/update-var-value "X" {:val :bar} ve)]
    (is (nil? (vars/is-unbound? "X" ve')))
    (is (not (vars/is-unbound? "X" ve')))))

(deftest add-constraint-test
  (let [ve  (vars/new-var-env)
        ve' (vars/add-var-constraint "X" :a ve)]
    (is (contains? (:constraints (vars/var-value "X" ve')) :a))))

(deftest unify-vars-both-unbound-test
  (let [ve  (vars/new-var-env)
        ve' (vars/unify-vars "X" "Y" ve)]
    ;; After unifying X and Y, binding X should bind Y too
    (let [ve'' (vars/update-var-value "X" {:val :foo} ve')]
      (is (= {:val :foo} (vars/var-value "Y" ve''))))))

(deftest generate-unique-var-test
  (let [ve (vars/new-var-env)
        [v1 ve1] (vars/generate-unique-var "A" ve)
        [v2 ve2] (vars/generate-unique-var "A" ve1)]
    (is (not= v1 v2))
    (is (string? v1))
    (is (string? v2))))

(deftest get-unique-vars-test
  (let [head {:op :p :args ["X" "Y"]}
        body [{:op :q :args ["X"]}]
        ve   (vars/new-var-env)
        [h2 b2 ve'] (vars/get-unique-vars head body ve)]
    ;; Head and body use renamed variables
    (is (not= "X" (first (:args h2))))
    (is (not= "Y" (second (:args h2))))
    ;; The same variable "X" in head and body gets the same fresh name
    (is (= (first (:args h2)) (first (:args (first b2)))))))

(deftest fill-in-test
  (let [ve  (vars/new-var-env)
        ve' (vars/update-var-value "X" {:val :hello} ve)]
    (is (= :hello (vars/fill-in "X" ve')))
    (is (= {:op :f :args [:hello :world]}
           (vars/fill-in {:op :f :args ["X" :world]} ve')))))
