(ns bigbuild
  (:require [scasp.main :as main]
            [scasp.program :as prog]
            [scasp.solver :as solver]))

(defn r [head body] (prog/make-rule head body))

(defn time-ms [thunk]
  (let [t0 (System/nanoTime) v (thunk)]
    [(/ (- (System/nanoTime) t0) 1e6) v]))

(defn bench-build [n]
  (let [rules (mapv (fn [i] (r {:op :item :args [i]} [])) (range n))
        q     [{:op :item :args [(dec n)]}]
        _     (System/gc)
        [bms prog] (time-ms #(main/build-program rules q #{} {:no-nmr true}))
        [sms res]  (time-ms #(count (take 1 (solver/run-query prog))))]
    (println (format "n=%-9d build %10.1f ms | solve %8.2f ms | clauses=%d res=%s"
                     n bms sms
                     (reduce + (map count (vals (:rules prog))))
                     (pr-str res)))))

(defn -main [& args]
  (bench-build 1000) ; warmup
  (doseq [n (map #(Long/parseLong %) args)]
    (bench-build n)))
