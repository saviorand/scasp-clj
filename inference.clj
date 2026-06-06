(load-file "fold.clj")

(ns inference
  "Port of inference.pl — unified deduction / abduction / induction
   over an ontology list, using scasp-clj and the FOLD-R algorithm."
  (:require [scasp.main    :as main]
            [scasp.program :as prog]
            [scasp.vars    :as vars]
            [scasp.term    :as term]
            [clojure.string :as str]))

;;; ── Term helpers ─────────────────────────────────────────────────────────────

(defn- c [op & args] {:op op :args (vec args)})
(defn- r [head & body] (prog/make-rule head (vec body)))

;;; ── Ontology helpers matching inference.pl ───────────────────────────────────

(defn- rule? [t] (contains? t :head))

(defn- term->rule
  "create_background: bare term map becomes a fact (rule with empty body)."
  [t]
  (if (rule? t) t (r t)))

(defn- extract-pos-neg
  "extract_pos_neg: pull positive(X) / negative(X) markers from ontology."
  [ontology]
  {:pos (into [] (keep #(when (= (:op %) :positive) (first (:args %))) ontology))
   :neg (into [] (keep #(when (= (:op %) :negative) (first (:args %))) ontology))})

(defn- extract-predicates
  "extract_predicates: all unique pred keywords except positive, negative, goal-kw.
   Skips terms with variable args — those are type hints, not ground facts."
  [ontology goal-kw]
  (->> ontology
       (remove #(some string? (:args %)))
       (map :op)
       (remove nil?)
       (remove #{:positive :negative goal-kw})
       distinct
       vec))

;;; ── Human-readable output matching scasp/human ──────────────────────────────

(defn- human-term
  "Format a ground term as natural language: 'pred holds for arg1, and arg2'."
  [t ve]
  (let [fill  (fn [x] (vars/fill-in x ve))
        grnd  (fn [x] (let [v (fill x)] (if (keyword? v) (name v) (str v))))
        op    (name (:op t))
        args  (mapv fill (:args t))]
    (cond
      (empty? args)
      (str op " holds")
      (= (count args) 1)
      (str op " holds for " (grnd (first args)))
      :else
      (let [all (mapv grnd args)
            butlast-s (str/join ", " (butlast all))]
        (str op " holds for " butlast-s ", and " (last all))))))

(defn- print-model
  "Print the answer set in human_model style: '• pred holds for ...' per entry."
  [chs ve]
  (doseq [[f entries] chs
          {:keys [args success?]} entries
          :when (and success?
                     (not (str/starts-with? (term/functor-name-str f) "_")))]
    (let [t {:op (keyword (term/functor-name-str f)) :args args}]
      (println (str "   • " (human-term t ve))))))

(declare print-just-tree)

(defn- internal-term?
  "True for NMR/dual/internal terms that should not appear in user output."
  [t]
  (when (map? t)
    (let [n (name (:op t))]
      (or (str/starts-with? n "_")
          (str/starts-with? n "not_")))))

(defn- print-just-tree
  "Recursively print justification tree in human_justification_tree style."
  [just ve indent]
  (let [pad (str (apply str (repeat indent "   ")))]
    (cond
      (or (nil? just) (= just :success) (= just :vacuous))
      nil

      (:chs-success just)
      (when-not (internal-term? (:chs-success just))
        (println (str pad "[Coinductive success]")))

      (:abduced just)
      (println (str pad "[Assumed] " (human-term (:abduced just) ve)))

      (:rule just)
      (let [head (:rule just)
            sub  (:sub-just just)]
        (when-not (internal-term? head)
          (if (or (nil? sub) (= sub :success))
            (println (str pad (human-term head ve)))
            (do
              (println (str pad (human-term head ve) ", because"))
              (print-just-tree sub ve (inc indent))))))

      (:forall just)
      (do
        (println (str pad "for all " (:forall just)))
        (print-just-tree (:body just) ve (inc indent)))

      ;; Sequence of body goals resolved left-to-right
      (sequential? just)
      (doseq [j just] (print-just-tree j ve indent))

      :else nil)))

(defn print-justification
  "Print Model and Justification Tree in the style of inference.pl's print_justification/2."
  [result]
  (let [{:keys [var-env chs just]} result]
    (println "Model:")
    (print-model chs var-env)
    (println "\nJustification Tree:")
    (print-just-tree just var-env 1)))

;;; ── inference/2 and inference/3 ──────────────────────────────────────────────

(defn inference
  "Unified inference matching inference.pl.

   (inference ontology goal-term)            ; deduction (default)
   (inference :deduction  ontology goal)     ; explicit deduction
   (inference :abduction  ontology goal)     ; abduction
   (inference :induction  ontology goal-kw)  ; induction via FOLD-R"
  ([ontology goal]
   (inference :deduction ontology goal))
  ([mode ontology goal]
   (case mode
     :deduction
     (let [rules (mapv term->rule ontology)]
       (main/solve-all rules [goal]))

     :abduction
     (let [rules   (mapv term->rule ontology)
           prog    (main/build-program rules [goal])
           defined (set (keys (:rules prog)))
           ;; Collect body goals from all rules — these are the calls that
           ;; may have no definition, making them abducible.
           body-goals (mapcat :body rules)
           abducibles (into #{}
                            (comp (map #(when (map? %)
                                          (str (name (:op %)) "/" (count (:args %)))))
                                  (remove nil?)
                                  (remove #(contains? defined %)))
                            body-goals)]
       (main/solve-all rules [goal] abducibles))

     :induction
     ;; goal here is a keyword (target predicate name), matching fold/8 signature
     (let [{:keys [pos neg]} (extract-pos-neg ontology)
           predicates        (extract-predicates ontology goal)
           background        (fold/propositionalize (mapv term->rule ontology))
           result            (fold/induce goal pos neg background predicates)]
       result))))

;;; ── Beans example ─────────────────────────────────────────────────────────────

(println "\n=== Deduction ===")
;; white(B) :- from(B, s1).  from(b1, s1).  ?- white(X).
(let [results (inference
               [(r (c :white "B") (c :from "B" :s1))
                (c :sack :s1)
                (c :bean :b1)
                (c :from :b1 :s1)]
               (c :white "X"))]
  (if (seq results)
    (doseq [res results] (print-justification res))
    (println "false.")))

(println "\n=== Abduction ===")
;; white(X) :- from(X, s1).  #abducible from/2.  ?- white(b1).
(let [results (inference
               :abduction
               [(r (c :white "X") (c :from "X" :s1))]
               (c :white :b1))]
  (if (seq results)
    (doseq [res results] (print-justification res))
    (println "false.")))

(println "\n=== Induction ===")
;; Exact ontology from inferenceExample.pl:
;; sack(s1), bean(b1), white(Y), from_s1(b1), positive(b1)
;; white(Y) is a type hint (Y unbound) — filtered out by extract-predicates/propositionalize
(let [result (inference
              :induction
              [(c :sack :s1)
               (c :bean :b1)
               (c :white "Y")   ; type hint — Y is a variable string, skipped as ground fact
               (c :from-s1 :b1)
               (c :positive :b1)]
              :white)]
  (println "Positive rules:")
  (doseq [rule (:positive-rules result)]
    (println " " rule))
  (println "Exception rules:")
  (doseq [rule (:exception-rules result)]
    (println " " rule)))
