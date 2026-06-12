(ns bench
  (:require [scasp.main :as main]
            [scasp.program :as prog]
            [scasp.solver :as solver]))

(defn c [op & args] {:op op :args (vec args)})
(defn r [head & body] (prog/make-rule head (vec body)))

(defn time-ms [thunk]
  (let [t0 (System/nanoTime) v (thunk)]
    [(/ (- (System/nanoTime) t0) 1e6) v]))

(defn report [label build-thunk solve-thunk]
  ;; build once (timed), then solve (timed) on the prebuilt program
  (let [[bms prog] (time-ms build-thunk)
        [sms res]  (time-ms #(solve-thunk prog))]
    (println (format "%-34s build %9.2f ms | solve %9.2f ms | res %s"
                     label bms sms (pr-str res)))))

(defn bench-facts [n]
  (let [rules (mapv (fn [i] (r (c :item i))) (range n))
        q     [(c :item (dec n))]]
    (report (str "facts n=" n)
            #(main/build-program rules q #{} {:no-nmr true})
            #(count (take 1 (solver/run-query %))))))

(defn bench-chain [n]
  (let [edges (mapv (fn [i] (r (c :edge i (inc i)))) (range n))
        rules (into edges
                    [(r (c :reach "X" "Y") (c :edge "X" "Y"))
                     (r (c :reach "X" "Y") (c :edge "X" "Z") (c :reach "Z" "Y"))])
        q     [(c :reach 0 n)]]
    (report (str "chain n=" n)
            #(main/build-program rules q #{} {:no-nmr true})
            #(count (take 1 (solver/run-query %))))))

(defn bench-ancestor [n]
  (let [facts (mapv (fn [i] (r (c :parent i (inc i)))) (range n))
        rules (into facts
                    [(r (c :ancestor "X" "Y") (c :parent "X" "Y"))
                     (r (c :ancestor "X" "Y") (c :parent "X" "Z") (c :ancestor "Z" "Y"))])
        q     [(c :ancestor 0 "Who")]]
    (report (str "ancestor n=" n)
            #(main/build-program rules q #{} {:no-nmr true})
            #(count (into [] (solver/run-query %))))))

(defn -main [& _]
  (bench-facts 100) (bench-chain 10)            ; warmup
  (println "\n=== Bench 1: facts (build vs solve) ===")
  (doseq [n [100 500 1000 2000 4000]] (bench-facts n))
  (println "\n=== Bench 2: chain reachability ===")
  (doseq [n [5 10 20 40 80 160]] (bench-chain n))
  (println "\n=== Bench 3: ancestor (all solutions) ===")
  (doseq [n [10 20 40 80 160]] (bench-ancestor n)))
