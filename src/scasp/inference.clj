(ns scasp.inference
  "Unified inference API matching inference.pl — deduction, abduction, induction.

   (inference ontology goal)               ; deduction (default)
   (inference :deduction  ontology goal)   ; explicit deduction
   (inference :abduction  ontology goal)   ; abduction — open predicates assumed
   (inference :induction  ontology goal-kw); induction via FOLD-R

   Ontology is a seq of scasp-clj term/rule maps.  Bare term maps are treated
   as facts (rules with empty body).  Variable args (strings) mark type hints
   and are ignored during propositionalization and predicate extraction.

   Human-readable output:
     (print-justification result)   ; Model + Justification Tree, Prolog style"
  (:require [scasp.main    :as main]
            [scasp.program :as prog]
            [scasp.fold    :as fold]
            [scasp.vars    :as vars]
            [scasp.term    :as term]
            [clojure.string :as str]))

;;; ── Ontology helpers ─────────────────────────────────────────────────────────

(defn- term->rule [t]
  (if (contains? t :head) t (prog/make-rule t [])))

(defn- extract-pos-neg
  "Pull positive(X) / negative(X) markers out of the ontology list."
  [ontology]
  {:pos (into [] (keep #(when (= (:op %) :positive) (first (:args %))) ontology))
   :neg (into [] (keep #(when (= (:op %) :negative) (first (:args %))) ontology))})

(defn- extract-predicates
  "All unique pred keywords except positive, negative, and goal-kw.
   Skips terms with variable (string) args — those are type hints."
  [ontology goal-kw]
  (->> ontology
       (remove #(some string? (:args %)))
       (map :op)
       (remove nil?)
       (remove #{:positive :negative goal-kw})
       distinct
       vec))

;;; ── Human-readable output ────────────────────────────────────────────────────

(defn- human-term [t ve]
  (let [fill (fn [x] (vars/fill-in x ve))
        grnd (fn [x] (let [v (fill x)] (if (keyword? v) (name v) (str v))))
        op   (name (:op t))
        args (mapv fill (:args t))]
    (cond
      (empty? args) (str op " holds")
      (= 1 (count args)) (str op " holds for " (grnd (first args)))
      :else (let [gs (mapv grnd args)]
              (str op " holds for " (str/join ", " (butlast gs)) ", and " (last gs))))))

(defn- internal? [t]
  (when (map? t)
    (let [n (name (:op t))]
      (or (str/starts-with? n "_") (str/starts-with? n "not_")))))

(defn- print-model [chs ve]
  (doseq [[f entries] chs
          {:keys [args success?]} entries
          :when (and success? (not (str/starts-with? (term/functor-name-str f) "_")))]
    (println (str "   • " (human-term {:op (keyword (term/functor-name-str f)) :args args} ve)))))

(declare print-just-tree)

(defn- print-just-tree [just ve indent]
  (let [pad (apply str (repeat indent "   "))]
    (cond
      (or (nil? just) (= just :success) (= just :vacuous)) nil
      (:chs-success just) (when-not (internal? (:chs-success just))
                            (println (str pad "[Coinductive success]")))
      (:abduced just)     (println (str pad "[Assumed] " (human-term (:abduced just) ve)))
      (:rule just)        (let [head (:rule just) sub (:sub-just just)]
                            (when-not (internal? head)
                              (if (or (nil? sub) (= sub :success))
                                (println (str pad (human-term head ve)))
                                (do (println (str pad (human-term head ve) ", because"))
                                    (print-just-tree sub ve (inc indent))))))
      (:forall just)      (do (println (str pad "for all " (:forall just)))
                              (print-just-tree (:body just) ve (inc indent)))
      (sequential? just)  (doseq [j just] (print-just-tree j ve indent)))))

(defn print-justification
  "Print Model and Justification Tree in the style of inference.pl's print_justification/2."
  [result]
  (let [{:keys [var-env chs just]} result]
    (println "Model:")
    (print-model chs var-env)
    (println "\nJustification Tree:")
    (print-just-tree just var-env 1)))

;;; ── inference ────────────────────────────────────────────────────────────────

(defn inference
  "Unified inference over an ontology list.

   Deduction / abduction return a seq of result maps (pass each to print-justification).
   Induction returns {:positive-rules [...] :exception-rules [...]}."
  ([ontology goal]
   (inference :deduction ontology goal))
  ([mode ontology goal]
   (case mode
     :deduction
     (main/solve-all (mapv term->rule ontology) [goal])

     :abduction
     (let [rules      (mapv term->rule ontology)
           prog       (main/build-program rules [goal])
           defined    (set (keys (:rules prog)))
           body-goals (mapcat :body rules)
           abducibles (into #{}
                            (comp (map #(when (map? %)
                                          (str (name (:op %)) "/" (count (:args %)))))
                                  (remove nil?)
                                  (remove #(contains? defined %)))
                            body-goals)]
       (main/solve-all rules [goal] abducibles))

     :induction
     (let [{:keys [pos neg]} (extract-pos-neg ontology)
           predicates        (extract-predicates ontology goal)
           background        (fold/propositionalize (mapv term->rule ontology))]
       (fold/induce goal pos neg background predicates)))))
