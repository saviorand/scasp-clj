(ns scasp.lang.parser
  "Tokenizer and parser for the s(CASP) surface language.

   Syntax:
     bird(tweety).                     # fact
     flies(X) <- bird(X), not ab(X).   # rule
     false <- p(X), q(X).              # integrity constraint
     ?- flies(X).                       # forward query
     ?- why flies(tweety).              # justification query
     ?- whynot flies(sam).              # failure explanation
     ?- solve flies(X).                 # enumerate all answers"
  (:require [clojure.string :as str]))

;;; ── Tokenizer ──────────────────────────────────────────────────────────────

(defn- whitespace? [c] (Character/isWhitespace ^char c))
(defn- letter? [c] (Character/isLetter ^char c))
(defn- digit? [c] (Character/isDigit ^char c))
(defn- id-char? [c] (or (Character/isLetterOrDigit ^char c) (= c \_)))

(defn- skip-ws-and-comments [^String s ^long i]
  (loop [i i]
    (cond
      (>= i (.length s)) i
      (whitespace? (.charAt s i)) (recur (inc i))
      (= (.charAt s i) \#)
      (let [nl (.indexOf s "\n" (int i))]
        (if (neg? nl) (.length s) (recur (inc nl))))
      :else i)))

(defn- read-ident [^String s ^long i]
  (let [sb (StringBuilder.)]
    (loop [i i]
      (if (and (< i (.length s)) (id-char? (.charAt s i)))
        (do (.append sb (.charAt s i)) (recur (inc i)))
        [(.toString sb) i]))))

(defn- read-number [^String s ^long i]
  (let [sb (StringBuilder.)]
    (loop [i i dot? false]
      (if (< i (.length s))
        (let [c (.charAt s i)]
          (cond
            (digit? c)
            (do (.append sb c) (recur (inc i) dot?))
            (and (= c \.) (not dot?)
                 (< (inc i) (.length s))
                 (digit? (.charAt s (inc i))))
            (do (.append sb c) (recur (inc i) true))
            :else
            [(if dot? (Double/parseDouble (.toString sb))
                      (Long/parseLong (.toString sb))) i]))
        [(if dot? (Double/parseDouble (.toString sb))
                  (Long/parseLong (.toString sb))) i]))))

(defn- peek2 [^String s ^long i]
  (when (< (inc i) (.length s))
    (str (.charAt s i) (.charAt s (inc i)))))

(defn tokenize [^String input]
  (let [len (.length input)]
    (loop [i 0 tokens []]
      (let [i (skip-ws-and-comments input i)]
        (if (>= i len)
          tokens
          (let [c (.charAt input i)
                p2 (peek2 input i)]
            (cond
              (= p2 "<-") (recur (+ i 2) (conj tokens {:type :arrow}))
              (= p2 "?-") (recur (+ i 2) (conj tokens {:type :query}))
              (= p2 "<=") (recur (+ i 2) (conj tokens {:type :op :value :=<}))
              (= p2 ">=") (recur (+ i 2) (conj tokens {:type :op :value :>=}))
              (= p2 "==") (recur (+ i 2) (conj tokens {:type :op :value :=:=}))
              (= p2 "!=") (recur (+ i 2) (conj tokens {:type :op :value :arith-ne}))

              (or (letter? c) (= c \_))
              (let [[id next-i] (read-ident input i)]
                (cond
                  (= id "_")
                  (recur next-i (conj tokens {:type :variable :value "_"}))
                  (Character/isUpperCase ^char (.charAt ^String id 0))
                  (recur next-i (conj tokens {:type :variable :value id}))
                  (= id "not")   (recur next-i (conj tokens {:type :not}))
                  (= id "is")    (recur next-i (conj tokens {:type :is}))
                  (= id "false") (recur next-i (conj tokens {:type :false}))
                  (= id "true")  (recur next-i (conj tokens {:type :true}))
                  :else (recur next-i (conj tokens {:type :atom :value id}))))

              (digit? c)
              (let [[n next-i] (read-number input i)]
                (recur next-i (conj tokens {:type :number :value n})))

              (= c \() (recur (inc i) (conj tokens {:type :lparen}))
              (= c \)) (recur (inc i) (conj tokens {:type :rparen}))
              (= c \,) (recur (inc i) (conj tokens {:type :comma}))
              (= c \.) (recur (inc i) (conj tokens {:type :dot}))
              (= c \<) (recur (inc i) (conj tokens {:type :op :value :<}))
              (= c \>) (recur (inc i) (conj tokens {:type :op :value :>}))
              (= c \+) (recur (inc i) (conj tokens {:type :op :value :+}))
              (= c \-) (recur (inc i) (conj tokens {:type :op :value :-}))
              (= c \*) (recur (inc i) (conj tokens {:type :op :value :*}))
              (= c \/) (recur (inc i) (conj tokens {:type :op :value :div}))
              (= c \=) (recur (inc i) (conj tokens {:type :op :value :=}))

              :else
              (throw (ex-info (str "Unexpected character: '" c "'")
                              {:char c :pos i})))))))))

;;; ── Parser state ────────────────────────────────────────────────────────────

(defn- make-parser [tokens]
  {:tokens tokens :pos (atom 0) :anon-counter (atom 0)})

(defn- peek-tok [p]
  (let [pos @(:pos p)]
    (when (< pos (count (:tokens p)))
      (nth (:tokens p) pos))))

(defn- next-tok! [p]
  (let [pos @(:pos p)
        tok (when (< pos (count (:tokens p)))
              (nth (:tokens p) pos))]
    (when tok (swap! (:pos p) inc))
    tok))

(defn- expect! [p type]
  (let [tok (next-tok! p)]
    (when (or (nil? tok) (not= (:type tok) type))
      (throw (ex-info (str "Expected " (name type) " but got "
                           (if tok (str (name (:type tok))
                                        (when (:value tok) (str " '" (:value tok) "'")))
                                   "end of input"))
                      {:expected type :got tok})))
    tok))

(defn- fresh-anon! [p]
  (str "_anon" (swap! (:anon-counter p) inc)))

;;; ── Recursive descent ───────────────────────────────────────────────────────

(declare parse-goal parse-expr parse-arith)

(def ^:private arith-ops #{:+ :- :* :div})
(def ^:private cmp-ops #{:< :> :=< :>= :=:= :arith-ne :=})

(defn- parse-arg-list [p]
  (expect! p :lparen)
  (loop [args []]
    (let [arg (parse-expr p)
          args (conj args arg)]
      (if (= (:type (peek-tok p)) :comma)
        (do (next-tok! p) (recur args))
        (do (expect! p :rparen) args)))))

(defn- parse-primary [p]
  (let [tok (peek-tok p)]
    (when-not tok
      (throw (ex-info "Unexpected end of input" {})))
    (case (:type tok)
      :atom
      (do (next-tok! p)
          (if (= (:type (peek-tok p)) :lparen)
            {:op (keyword (:value tok)) :args (parse-arg-list p)}
            (keyword (:value tok))))

      :variable
      (do (next-tok! p)
          (if (= (:value tok) "_")
            (fresh-anon! p)
            (:value tok)))

      :number
      (do (next-tok! p) (:value tok))

      :true
      (do (next-tok! p) {:op :true :args []})

      :false
      (do (next-tok! p) {:op :false :args []})

      :lparen
      (do (next-tok! p)
          (let [e (parse-expr p)]
            (expect! p :rparen)
            e))

      :op
      (if (= (:value tok) :-)
        (do (next-tok! p)
            (let [inner (parse-primary p)]
              (if (number? inner)
                (- inner)
                {:op :- :args [inner]})))
        (throw (ex-info (str "Unexpected operator: " (:value tok)) {:token tok})))

      (throw (ex-info (str "Unexpected token: " (name (:type tok))
                           (when (:value tok) (str " '" (:value tok) "'")))
                      {:token tok})))))

(defn- parse-arith [p]
  (let [left (parse-primary p)
        tok (peek-tok p)]
    (if (and tok (= (:type tok) :op) (contains? arith-ops (:value tok)))
      (do (next-tok! p)
          {:op (:value tok) :args [left (parse-primary p)]})
      left)))

(defn- parse-expr [p]
  (let [left (parse-arith p)
        tok (peek-tok p)]
    (cond
      (and tok (= (:type tok) :is))
      (do (next-tok! p)
          {:op :is :args [left (parse-arith p)]})

      (and tok (= (:type tok) :op) (contains? cmp-ops (:value tok)))
      (do (next-tok! p)
          {:op (:value tok) :args [left (parse-arith p)]})

      :else left)))

(defn- ensure-compound
  "In goal position, bare keywords become zero-arity compounds."
  [term]
  (if (keyword? term) {:op term :args []} term))

(defn- parse-goal [p]
  (if (= (:type (peek-tok p)) :not)
    (do (next-tok! p)
        {:op :not :args [(ensure-compound (parse-goal p))]})
    (ensure-compound (parse-expr p))))

(defn- parse-goal-list [p]
  (loop [goals [(parse-goal p)]]
    (if (and (peek-tok p) (= (:type (peek-tok p)) :comma))
      (do (next-tok! p) (recur (conj goals (parse-goal p))))
      goals)))

;;; ── Statement parsing ───────────────────────────────────────────────────────

(defn parse-statement [p]
  (let [tok (peek-tok p)]
    (when-not tok
      (throw (ex-info "Unexpected end of input" {})))
    (cond
      (= (:type tok) :query)
      (do (next-tok! p)
          (let [next-t (peek-tok p)
                mode (if (and next-t (= (:type next-t) :atom)
                              (contains? #{"why" "whynot" "solve"} (:value next-t)))
                       (do (next-tok! p) (keyword (:value next-t)))
                       :forward)
                goals (parse-goal-list p)]
            (expect! p :dot)
            {:type :query :mode mode :goals goals}))

      (= (:type tok) :false)
      (let [_ (next-tok! p)
            next-t (peek-tok p)]
        (if (and next-t (= (:type next-t) :arrow))
          (do (next-tok! p)
              (let [body (parse-goal-list p)]
                (expect! p :dot)
                {:type :constraint :data {:head {:op :_false :args []} :body body}}))
          (do (expect! p :dot)
              {:type :fact :data {:head {:op :false :args []} :body []}})))

      :else
      (let [head (ensure-compound (parse-expr p))
            next-t (peek-tok p)]
        (if (and next-t (= (:type next-t) :arrow))
          (do (next-tok! p)
              (let [body (parse-goal-list p)]
                (expect! p :dot)
                {:type :rule :data {:head head :body body}}))
          (do (expect! p :dot)
              {:type :fact :data {:head head :body []}}))))))

;;; ── Top-level API ───────────────────────────────────────────────────────────

(defn parse-all
  "Parse all statements from a string."
  [input]
  (let [tokens (tokenize input)
        p (make-parser tokens)]
    (loop [stmts []]
      (if (nil? (peek-tok p))
        stmts
        (recur (conj stmts (parse-statement p)))))))

(defn parse-program
  "Parse a program string into {:rules [...] :queries [...]}."
  [input]
  (let [stmts (parse-all input)]
    {:rules   (vec (keep (fn [s]
                           (when (#{:fact :rule :constraint} (:type s))
                             (:data s)))
                         stmts))
     :queries (vec (filter #(= (:type %) :query) stmts))}))
