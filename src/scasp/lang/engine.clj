(ns scasp.lang.engine
  "Multi-directional query engine wrapping s(CASP) core.

   Supports forward queries, justification (why), failure explanation (whynot),
   and solution enumeration (solve)."
  (:require [scasp.main   :as scasp]
            [scasp.vars   :as vars]
            [scasp.output :as output]))

(defn query-forward
  "Run a forward query. Returns seq of result maps."
  [rules goals]
  (scasp/solve-all rules goals))

(defn query-whynot
  "Query why goals fail by solving their negation (dual).
   Returns results whose justification trees explain the failure."
  [rules goals]
  (let [negated (mapv (fn [g] {:op :not :args [g]}) goals)]
    (scasp/solve-all rules negated)))

(defn extract-bindings
  "Extract variable bindings from a result."
  [result var-names]
  (scasp/result-bindings result var-names))

(defn format-binding
  "Format a single variable's value as a string."
  [var-name result]
  (let [ve (:var-env result)
        val (vars/fill-in var-name ve)]
    (output/fmt-term val ve)))
