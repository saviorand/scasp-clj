(ns scasp.lang.repl
  "Interactive REPL for s(CASP) Lang."
  (:require [clojure.string    :as str]
            [scasp.lang.parser :as parser]
            [scasp.lang.engine :as engine]
            [scasp.lang.format :as fmt]
            [scasp.output      :as output]
            [scasp.vars        :as vars]))

;;; ── Display helpers ─────────────────────────────────────────────────────────

(defn- print-banner []
  (println)
  (println "  s(CASP) Lang REPL")
  (println "  Write rules once. Query from any direction.")
  (println "  Type :help for commands, :quit to exit.")
  (println))

(defn- print-help []
  (println)
  (println "  Syntax:")
  (println "    bird(tweety).                     # fact")
  (println "    flies(X) <- bird(X), not ab(X).   # rule")
  (println "    false <- p(X), q(X).              # integrity constraint")
  (println)
  (println "  Queries:")
  (println "    ?- flies(X).                      # forward: find answers")
  (println "    ?- why flies(tweety).             # explain why it holds")
  (println "    ?- whynot flies(sam).             # explain why it fails")
  (println "    ?- solve flies(X).                # all answers with models")
  (println)
  (println "  Terms:")
  (println "    lowercase  = atoms      (tweety, bird, sam)")
  (println "    Uppercase  = variables  (X, Age, Who)")
  (println "    not term   = negation-as-failure")
  (println "    Comparisons: <  >  <=  >=  ==  !=")
  (println "    Arithmetic:  X is Y + 1")
  (println)
  (println "  Commands:")
  (println "    :help          this help")
  (println "    :list          show loaded rules")
  (println "    :clear         clear all rules")
  (println "    :load <file>   load program from file")
  (println "    :run  <file>   load and run all queries in file")
  (println "    :quit          exit")
  (println))

(defn- format-rule [{:keys [head body]}]
  (let [ve (vars/new-var-env)
        head-str (output/fmt-term head ve)]
    (if (empty? body)
      (str head-str ".")
      (str head-str " <- "
           (str/join ", " (map #(output/fmt-term % ve) body))
           "."))))

;;; ── Query execution ─────────────────────────────────────────────────────────

(defn- handle-query [rules mode goals]
  (try
    (case mode
      :forward
      (fmt/print-results (engine/query-forward rules goals)
                         goals {})

      :why
      (fmt/print-results (engine/query-forward rules goals)
                         goals {:show-just? true :show-model? true})

      :whynot
      (fmt/print-whynot (engine/query-whynot rules goals) goals)

      :solve
      (fmt/print-results (engine/query-forward rules goals)
                         goals {:show-model? true}))
    (catch Exception e
      (println (str "  Query error: " (.getMessage e))))))

;;; ── File operations ─────────────────────────────────────────────────────────

(defn- load-file-rules [filepath]
  (let [content (slurp filepath)
        parsed (parser/parse-program content)]
    (:rules parsed)))

(defn- load-into [rules filepath]
  (try
    (let [new-rules (load-file-rules filepath)]
      (println (str "  Loaded " (count new-rules) " rules/facts from " filepath))
      (into rules new-rules))
    (catch Exception e
      (println (str "  Error: " (.getMessage e)))
      rules)))

(defn run-file
  "Parse and execute a file, running all embedded queries."
  [filepath]
  (let [content (slurp filepath)
        parsed (parser/parse-program content)
        rules (:rules parsed)
        queries (:queries parsed)]
    (println (str "Loaded " (count rules) " rules/facts from " filepath))
    (doseq [q queries]
      (println)
      (let [mode-str (if (= (:mode q) :forward) "" (str " (" (name (:mode q)) ")"))]
        (println (str "?- "
                      (str/join ", "
                                (map #(output/fmt-term % (vars/new-var-env)) (:goals q)))
                      "." mode-str)))
      (handle-query rules (:mode q) (:goals q)))))

;;; ── Input reading ───────────────────────────────────────────────────────────

(defn- read-statement
  "Read a complete statement, accumulating lines until we see a period."
  []
  (print "> ")
  (flush)
  (when-let [first-line (read-line)]
    (let [trimmed (str/trim first-line)]
      (if (or (str/blank? trimmed)
              (str/starts-with? trimmed ":")
              (str/ends-with? trimmed "."))
        trimmed
        (loop [acc trimmed]
          (print "  ")
          (flush)
          (if-let [line (read-line)]
            (let [full (str acc " " (str/trim line))]
              (if (str/ends-with? (str/trim line) ".")
                full
                (recur full)))
            acc))))))

;;; ── REPL loop ───────────────────────────────────────────────────────────────

(defn run-repl
  "Start the interactive REPL."
  ([] (run-repl []))
  ([initial-rules]
   (print-banner)
   (loop [rules (vec initial-rules)]
     (when-let [input (read-statement)]
       (cond
         (str/blank? input)
         (recur rules)

         (= input ":quit")
         (println "  Goodbye.")

         (= input ":help")
         (do (print-help) (recur rules))

         (= input ":list")
         (do (if (empty? rules)
               (println "  No rules loaded.")
               (doseq [r rules]
                 (println (str "  " (format-rule r)))))
             (recur rules))

         (= input ":clear")
         (do (println "  Rules cleared.") (recur []))

         (str/starts-with? input ":load ")
         (recur (load-into rules (str/trim (subs input 6))))

         (str/starts-with? input ":run ")
         (do (try (run-file (str/trim (subs input 5)))
                  (catch Exception e (println (str "  Error: " (.getMessage e)))))
             (recur rules))

         :else
         (let [rules' (try
                        (let [stmts (parser/parse-all input)]
                          (reduce
                            (fn [rs s]
                              (case (:type s)
                                (:fact :rule :constraint)
                                (do (println (str "  Added: " (format-rule (:data s))))
                                    (conj rs (:data s)))
                                :query
                                (do (handle-query rs (:mode s) (:goals s))
                                    rs)))
                            rules stmts))
                        (catch Exception e
                          (println (str "  Error: " (.getMessage e)))
                          rules))]
           (recur rules')))))))

(defn -main [& args]
  (if (seq args)
    (run-file (first args))
    (run-repl)))
