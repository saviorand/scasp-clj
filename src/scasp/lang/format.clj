(ns scasp.lang.format
  "Human-readable output formatting for s(CASP) Lang results.

   Formats variable bindings, justification trees (why),
   and failure explanations (whynot) as readable text.
   Internal s(CASP) predicates (_not_X_N, _nmr_check, etc.)
   are collapsed or hidden for clarity."
  (:require [clojure.string :as str]
            [scasp.output :as output]
            [scasp.vars   :as vars]
            [scasp.term   :as term]))

(defn format-term [t ve]
  (output/fmt-term t ve))

;;; ── Internal predicate detection ────────────────────────────────────────────

(defn- internal-head?
  "True if a rule head string represents an internal s(CASP) predicate."
  [head-str]
  (or (str/starts-with? head-str "_")
      (str/starts-with? head-str "(")
      (= head-str "_nmr_check")))

(defn- nmr-node?
  "True if a justification node is an NMR check (noise for the user)."
  [just ve]
  (and (:rule just)
       (let [s (format-term (:rule just) ve)]
         (str/includes? s "_nmr_check"))))

(defn- disequality-node?
  "True if a justification node represents a disequality check."
  [just ve]
  (and (:rule just)
       (let [s (format-term (:rule just) ve)]
         (str/includes? s "\\="))))

(defn- format-disequality
  "Format a disequality like (a \\= b) as 'a != b'."
  [s]
  (-> s
      (str/replace #"\((\S+) \\= (\S+)\)" "$1 != $2")
      (str/replace "\\=" "!=")))

;;; ── Justification tree formatting ───────────────────────────────────────────

(declare just-tree-lines)

(defn- collapse-internal
  "If a rule node has an internal head, skip it and return its children directly."
  [just ve prefix is-last?]
  (let [sub (:sub-just just)]
    (if (or (nil? sub) (= sub :success) (and (sequential? sub) (empty? sub)))
      []
      (let [children (if (sequential? sub) sub [sub])
            n (count children)]
        (vec (mapcat (fn [i child]
                       (just-tree-lines child ve prefix (= i (dec n))))
                     (range) children))))))

(defn- just-tree-lines
  "Convert a justification tree to indented lines with ASCII tree-drawing."
  [just ve prefix is-last?]
  (let [connector (if is-last? "`-- " "|-- ")
        extension (if is-last? "    " "|   ")]
    (cond
      (nil? just) []
      (= just :success) []
      (= just :vacuous) [(str prefix connector "[vacuous]")]

      (:chs-success just)
      [(str prefix connector "[coinductive success]")]

      (:abduced just)
      [(str prefix connector (format-term (:abduced just) ve) "  [assumed]")]

      (:forall just)
      (into [(str prefix connector "forall " (:forall just))]
            (just-tree-lines (:body just) ve (str prefix extension) true))

      (:findall just)
      [(str prefix connector "findall(...)")]

      (:rule just)
      (let [head-str (format-term (:rule just) ve)]
        (cond
          (str/includes? head-str "_nmr_check")
          []

          (internal-head? head-str)
          (collapse-internal just ve prefix is-last?)

          (str/includes? head-str "\\=")
          [(str prefix connector (format-disequality head-str))]

          :else
          (let [sub (:sub-just just)]
            (if (or (nil? sub) (= sub :success)
                    (and (sequential? sub) (empty? sub)))
              [(str prefix connector head-str "  [fact]")]
              (let [children (if (sequential? sub) sub [sub])
                    children (remove (fn [c]
                                       (and (map? c) (:rule c)
                                            (str/includes? (format-term (:rule c) ve) "_nmr_check")))
                                     children)
                    children (vec children)
                    n (count children)]
                (into [(str prefix connector head-str)]
                      (mapcat (fn [i child]
                                (just-tree-lines child ve
                                                 (str prefix extension)
                                                 (= i (dec n))))
                              (range) children)))))))

      (sequential? just)
      (let [filtered (remove (fn [j]
                               (and (map? j) (:rule j)
                                    (str/includes? (format-term (:rule j) ve) "_nmr_check")))
                             just)
            items (vec filtered)
            n (count items)]
        (vec (mapcat (fn [i j]
                       (just-tree-lines j ve prefix (= i (dec n))))
                     (range) items)))

      (map? just)
      [(str prefix connector
            (let [s (format-term just ve)]
              (if (str/includes? s "\\=")
                (format-disequality s)
                s)))]

      :else [(str prefix connector (pr-str just))])))

(defn format-justification
  "Format a justification tree as a multi-line string."
  [just ve]
  (str/join "\n" (just-tree-lines just ve "" true)))

;;; ── Result display ──────────────────────────────────────────────────────────

(defn- format-model [chs ve]
  (let [literals
        (for [[f entries] chs
              {:keys [args success?]} entries
              :when (and success?
                         (not (str/starts-with? (term/functor-name-str f) "_"))
                         (not (str/starts-with? (term/functor-name-str f) "not_")))]
          (if (empty? args)
            (term/functor-name-str f)
            (str (term/functor-name-str f)
                 "(" (str/join ", " (map #(format-term % ve) args)) ")")))]
    (when (seq literals)
      (str "{ " (str/join ", " (sort literals)) " }"))))

(defn print-result
  "Print a single query result."
  [n result goals {:keys [show-just? show-model?]}]
  (let [ve (:var-env result)
        qvars (output/collect-query-vars goals)]
    (if (seq qvars)
      (println (str "  Answer " n ": "
                    (str/join ", "
                              (map (fn [v]
                                     (let [val (vars/fill-in v ve)]
                                       (str v " = " (format-term val ve))))
                                   qvars))))
      (println (str "  Answer " n ": true")))
    (when show-model?
      (when-let [m (format-model (:chs result) ve)]
        (println (str "  Model: " m))))
    (when show-just?
      (println "  Justification:")
      (let [tree (format-justification (:just result) ve)]
        (when-not (str/blank? tree)
          (doseq [line (str/split-lines tree)]
            (println (str "    " line))))))))

(defn print-results
  "Print all results for a query."
  [results goals opts]
  (if (seq results)
    (doseq [[i r] (map-indexed vector results)]
      (print-result (inc i) r goals opts))
    (println "  No answers.")))

(defn print-whynot
  "Print explanation of why a query fails."
  [dual-results original-goals]
  (if (seq dual-results)
    (let [r (first dual-results)
          ve (:var-env r)
          just (:just r)]
      (println (str "  "
                    (str/join ", " (map #(format-term % (vars/new-var-env)) original-goals))
                    " does not hold because:"))
      (let [tree (format-justification just ve)]
        (when-not (str/blank? tree)
          (doseq [line (str/split-lines tree)]
            (println (str "    " line))))))
    (println "  (Could not construct failure explanation -- the goal may actually hold.)")))
