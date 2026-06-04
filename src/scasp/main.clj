(ns scasp.main
  "CLI entry point for scasp-clj.

   Usage:
     clj -M -m scasp.main [options] <file.pl>

   Options:
     -n <N>         Find N answer sets (default: 1; 0 = all)
     --tree         Print justification tree
     --quiet        Suppress answer set output (just count)
     --code         Print compiled program (after duals + NMR)"
  (:require [scasp.parser  :as parser]
            [scasp.duals   :as duals]
            [scasp.nmr     :as nmr]
            [scasp.solver  :as solver]
            [scasp.output  :as output]
            [scasp.program :as prog]
            [scasp.vars    :as vars]
            [clojure.string :as str])
  (:gen-class))

;;; ── Option parsing ───────────────────────────────────────────────────────────

(defn- parse-opts
  "Parse CLI args, returning {:file … :n … :tree? … :quiet? … :code? …}."
  [args]
  (loop [args args opts {:n 1 :tree? false :quiet? false :code? false :file nil}]
    (cond
      (empty? args) opts

      (= (first args) "-n")
      (recur (drop 2 args) (assoc opts :n (Integer/parseInt (second args))))

      (= (first args) "--tree")
      (recur (rest args) (assoc opts :tree? true))

      (= (first args) "--quiet")
      (recur (rest args) (assoc opts :quiet? true))

      (= (first args) "--code")
      (recur (rest args) (assoc opts :code? true))

      :else
      (recur (rest args) (assoc opts :file (first args))))))

;;; ── Program printing ─────────────────────────────────────────────────────────

(defn- print-program [program]
  (println "\n;; === Compiled Program ===")
  (doseq [[f rules] (:rules program)]
    (doseq [{:keys [head body]} rules]
      (if (empty? body)
        (println (str (output/fmt-term head (vars/new-var-env)) "."))
        (println (str (output/fmt-term head (vars/new-var-env))
                      " :-\n    "
                      (str/join ",\n    "
                                (map #(output/fmt-term % (vars/new-var-env)) body))
                      "."))))))

;;; ── Load + compile pipeline ──────────────────────────────────────────────────

(defn load-program
  "Parse, compile duals, generate NMR check.  Returns ready program."
  [source]
  (-> source
      parser/parse-program
      duals/compile-duals
      nmr/generate-nmr-check))

(defn load-file
  [path]
  (load-program (slurp path)))

;;; ── Run and print results ────────────────────────────────────────────────────

(defn run
  "Run the program and print up to n answer sets."
  [program opts]
  (let [n       (:n opts)
        query   (prog/defined-query program)
        results (solver/run-query program)
        results' (if (pos? n) (take n results) results)]
    (if (seq results')
      (do
        (doseq [[idx r] (map-indexed #(vector (inc %1) %2) results')]
          (when-not (:quiet? opts)
            (output/print-answer idx r query {:tree (:tree? opts)}))))
      (println "false."))))

;;; ── Main ─────────────────────────────────────────────────────────────────────

(defn -main [& args]
  (let [opts (parse-opts args)]
    (when-not (:file opts)
      (println "Usage: scasp [options] <file.pl>")
      (println "  -n <N>    Number of answer sets (0=all, default 1)")
      (println "  --tree    Show justification tree")
      (println "  --quiet   Suppress output, just count")
      (println "  --code    Print compiled program")
      (System/exit 1))
    (try
      (let [program (load-file (:file opts))]
        (when (:code? opts)
          (print-program program))
        (run program opts))
      (catch clojure.lang.ExceptionInfo e
        (binding [*out* *err*]
          (println "Error:" (.getMessage e))
          (println "Details:" (ex-data e)))
        (System/exit 2))
      (catch Exception e
        (binding [*out* *err*]
          (.printStackTrace e))
        (System/exit 2)))))
