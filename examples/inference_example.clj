;; examples/inference_example.clj
;;
;; Deduction, abduction, and induction over the beans ontology.
;; Mirrors the three ?- inference(...) queries from inferenceExample.pl.
;;
;; Load into a REPL (with src/ on the classpath) and eval the comment blocks.

(ns inference-example
  (:require [scasp.inference :refer [inference print-justification]]))

;;; ── Deduction ────────────────────────────────────────────────────────────────
;;
;; ?- inference([
;;     sack(s1),
;;     bean(X), white(Y), from(X,Z), bean(B),   % type hints
;;     white(B) :- from(B,s1),                  % rule
;;     from(b1,s1)                               % case
;; ], white(X)).
;; Deduced Result: white(b1)

(def deduction-ontology
  [{:op :sack  :args [:s1]}
   {:op :bean  :args ["X"]}                       ; type hint
   {:op :white :args ["Y"]}                       ; type hint
   {:op :from  :args ["X" "Z"]}                   ; type hint
   {:op :bean  :args ["B"]}                       ; type hint
   {:head {:op :white :args ["B"]}                ; white(B) :- from(B, s1)
    :body [{:op :from :args ["B" :s1]}]}
   {:op :from :args [:b1 :s1]}])                  ; from(b1, s1)

(def deduction-query {:op :white :args ["X"]})

(comment
  ;; Expected: one result, white holds for b1.
  (doseq [r (inference deduction-ontology deduction-query)]
    (print-justification r)))

;;; ── Induction ────────────────────────────────────────────────────────────────
;;
;; ?- inference(induction, [
;;     sack(s1),
;;     bean(b1),
;;     white(Y),                                 % type hint
;;     from_s1(b1),                              % case
;;     positive(b1)                              % positive example
;; ], white).
;; Induced "Rule": white(X) :- from_s1(X)

(def induction-ontology
  [{:op :sack     :args [:s1]}
   {:op :bean     :args [:b1]}
   {:op :white    :args ["Y"]}                    ; type hint
   {:op :from_s1  :args [:b1]}                    ; case: b1 is from s1
   {:op :positive :args [:b1]}])                  ; positive example

(comment
  ;; Expected: {:positive-rules [{white(X) :- from_s1(X)}] :exception-rules []}
  (inference :induction induction-ontology :white))

;;; ── Abduction ────────────────────────────────────────────────────────────────
;;
;; #abducible from(X,Z).
;; ?- inference(abduction, [
;;     white(X) :- from(X,s1)
;; ], white(b1)).
;; Abduced "Case": from(b1, s1)
;;
;; from/2 is undefined in the ontology so it is auto-detected as abducible.

(def abduction-ontology
  [{:head {:op :white :args ["X"]}                ; white(X) :- from(X, s1)
    :body [{:op :from :args ["X" :s1]}]}])

(def abduction-query {:op :white :args [:b1]})

(comment
  ;; Expected: one result with from(b1,s1) assumed.
  (doseq [r (inference :abduction abduction-ontology abduction-query)]
    (print-justification r)))
