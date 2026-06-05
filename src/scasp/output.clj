(ns scasp.output
  "Answer set printing and justification output."
  (:require [clojure.string :as str]
            [scasp.term  :as term]
            [scasp.vars  :as vars]))

;;; ── Forward declarations ─────────────────────────────────────────────────────

(declare fmt-term fmt-list)

;;; ── Term formatting ───────────────────────────────────────────────────────────

(def ^:private infix-ops
  #{:= :ne :is :=:= :arith-ne :< :> :=< :>= :term< :term> :term<= :term>=
    :+ :- :* :div :idiv :rem :mod :hat :pow :and :or})

(defn fmt-term
  "Produce a human-readable string for term t, filling in ve bindings."
  [t ve]
  (cond
    (term/is-var? t)
    (let [v (vars/var-value t ve)]
      (if (contains? v :val)
        (fmt-term (:val v) ve)
        (let [cs     (:constraints v)
              bounds (:numeric-bounds v)
              neq    (:numeric-neq v)
              +inf   Double/POSITIVE_INFINITY
              -inf   Double/NEGATIVE_INFINITY
              dis-parts (map #(str "\\=" (fmt-term % ve)) cs)
              num-parts (when bounds
                          (let [{:keys [lo hi lo-open? hi-open?]} bounds
                                lo-part (when (not= lo -inf)
                                          (str t (if lo-open? ">" ">=") lo))
                                hi-part (when (not= hi +inf)
                                          (str t (if hi-open? "<" "<=") hi))
                                neq-parts (map #(str t "=\\=" %) neq)]
                            (filter some? (concat [lo-part hi-part] neq-parts))))
              all-parts (concat dis-parts num-parts)]
          (if (empty? all-parts)
            t
            (str t "{" (str/join "," all-parts) "}")))))

    (term/is-atom? t)
    (let [n (name t)]
      (cond
        (str/starts-with? n "not_") (str "not " (subs n 4))
        :else                        n))

    (number? t)
    (str t)

    (term/is-naf? t)
    (str "not " (fmt-term (first (:args t)) ve))

    (term/is-forall? t)
    (str "forall(" (fmt-term (first (:args t)) ve)
         ", " (fmt-term (second (:args t)) ve) ")")

    (term/is-compound? t)
    (let [op-name (name (:op t))
          args    (:args t)]
      (cond
        ;; cons list
        (= (:op t) :cons)
        (fmt-list t ve)

        ;; infix binary operator
        (and (= (count args) 2)
             (contains? infix-ops (:op t)))
        (let [op-str (or (get term/op-kw->str (:op t)) op-name)]
          (str "(" (fmt-term (first args) ve)
               " " op-str " "
               (fmt-term (second args) ve) ")"))

        ;; unary minus
        (and (= (:op t) :-) (= (count args) 1))
        (str "-" (fmt-term (first args) ve))

        ;; internal not_ prefix → strip for output
        (str/starts-with? op-name "not_")
        (str "not " (subs op-name 4)
             (when (seq args)
               (str "(" (str/join ", " (map #(fmt-term % ve) args)) ")")))

        ;; empty list atom
        (= (:op t) (keyword "[]"))
        "[]"

        ;; regular compound
        :else
        (str op-name
             (when (seq args)
               (str "(" (str/join ", " (map #(fmt-term % ve) args)) ")")))))

    :else (pr-str t)))

(defn- fmt-list [t ve]
  (loop [items [] t' t]
    (cond
      (= t' (keyword "[]"))
      (str "[" (str/join ", " (map #(fmt-term % ve) items)) "]")

      (and (term/is-compound? t') (= (:op t') :cons))
      (let [[h tl] (:args t')]
        (recur (conj items h) tl))

      :else
      (str "[" (str/join ", " (map #(fmt-term % ve) items))
           "|" (fmt-term t' ve) "]"))))

;;; ── CHS / answer set printing ────────────────────────────────────────────────

(defn- visible-entry?
  "True if a CHS entry should be printed (success=true, not internal)."
  [functor {:keys [success?]}]
  (and success?
       (not (str/starts-with? (term/functor-name-str functor) "_"))))

(defn print-chs
  "Print the answer set (set of selected literals)."
  [chs ve]
  (let [literals
        (for [[f entries] chs
              e entries
              :when (visible-entry? f e)]
          (let [op   (term/functor-name-str f)
                args (:args e)]
            (if (empty? args)
              op
              (str op "(" (str/join ", " (map #(fmt-term % ve) args)) ")"))))]
    (when (seq literals)
      (println (str "{ " (str/join ", " (sort literals)) " }")))))

;;; ── Query variable bindings ──────────────────────────────────────────────────

(defn collect-query-vars
  "Extract distinct top-level variable names from goal list."
  [goals]
  (into [] (distinct (mapcat #(term/term-vars-list %) goals))))

(defn print-vars
  "Print query variable bindings."
  [query-vars ve]
  (doseq [v query-vars]
    (let [val (vars/fill-in v ve)]
      (println (str v " = " (fmt-term val ve))))))

;;; ── Justification tree ───────────────────────────────────────────────────────

(defn print-justification
  "Print a justification tree with indentation."
  ([just] (print-justification just 0))
  ([just indent]
   (let [pad (apply str (repeat (* 2 indent) " "))]
     (when (and just (not= just :success))
       (cond
         (:chs-success just)
         (println (str pad "[Coinductive success]"))

         (:rule just)
         (do
           (println (str pad (fmt-term (:rule just) (vars/new-var-env))))
           (print-justification (:sub-just just) (inc indent)))

         (:forall just)
         (do
           (println (str pad "forall " (:forall just)))
           (print-justification (:body just) (inc indent))))))))

;;; ── Answer printer ───────────────────────────────────────────────────────────

(defn print-answer
  "Print a single answer set from a solver result."
  [n result query-goals opts]
  (let [{:keys [var-env chs just]} result
        qvars (collect-query-vars query-goals)]
    (println (str "Answer: " n))
    (print-chs chs var-env)
    (print-vars qvars var-env)
    (when (:tree opts)
      (print-justification just))
    (newline)))
