(ns scasp.parser
  "Hand-written tokenizer + recursive-descent parser for s(CASP)/Prolog syntax.

   Parses programs with:
     - Facts:         p(a).
     - Rules:         h :- b1, b2, not b3.
     - Queries:       ?- goal.
     - Constraints:   :- body.      (headless / integrity constraints)
     - Classical neg: -p(X).
     - Directives:    #show p/1.  #abducible ab/1.  #domain n(X).
     - Comments:      % to end of line  /* … */
     - Operators:     is, =, \\=, =:=, =\\=, <, >, =<, >=, @<, @>, not
     - Lists:         [H|T], [a,b,c], []"
  (:require [clojure.string :as str]
            [scasp.term    :as term]
            [scasp.program :as prog]))

;;; ═══════════════════════════════════════════════════════════════════════════
;;; Tokenizer
;;; ═══════════════════════════════════════════════════════════════════════════

(def ^:private token-patterns
  [[:comment-line  #"(?s)%[^\n]*"]
   [:comment-block #"(?s)/\*.*?\*/"]
   [:ws            #"\s+"]
   [:float         #"-?\d+\.\d+([eE][+-]?\d+)?"]
   [:integer       #"-?\d+"]
   [:string        #"\"(?:[^\"\\]|\\.)*\""]
   [:quoted-atom   #"'(?:[^'\\]|\\.)*'"]
   [:op2           #"\\=|=\.\.|=:=|=\\=|@=<|@>=|@<|@>|:=|\.=\.|=<|>=|<=|=>|->|==|\\==|<>"]
   [:op1           #"[=<>\\!@#$&^~]+|:-|,|\||\?-|\.\."]
   [:lparen        #"\("]
   [:rparen        #"\)"]
   [:lbracket      #"\["]
   [:rbracket      #"\]"]
   [:pipe          #"\|"]
   [:comma         #","]
   [:dot           #"\.(?:\s|$)"]
   [:hash          #"#[a-z_]+"]
   [:neg-sign      #"-(?=[a-z_A-Z])"]  ; classical negation
   [:atom          #"[a-z_][a-zA-Z0-9_]*"]
   [:var           #"[A-Z_][a-zA-Z0-9_]*"]])

(defn- tokenize
  "Convert input string to a vector of {:type :val} tokens (skipping whitespace/comments)."
  [^String input]
  (loop [pos 0 tokens []]
    (if (>= pos (count input))
      tokens
      (let [sub (subs input pos)]
        (if-let [[typ re] (some (fn [[t r]] (let [m (re-matcher r sub)]
                                              (when (.lookingAt m) [t m])))
                                token-patterns)]
          (let [matched (.group ^java.util.regex.Matcher re)]
            (if (contains? #{:ws :comment-line :comment-block} typ)
              (recur (+ pos (count matched)) tokens)
              (recur (+ pos (count matched))
                     (conj tokens {:type typ :val matched}))))
          (throw (ex-info "Tokenizer: unexpected character"
                          {:pos pos :char (subs input pos (min (inc pos) (count input)))})))))))

;;; ═══════════════════════════════════════════════════════════════════════════
;;; Parser state
;;; ═══════════════════════════════════════════════════════════════════════════

(defrecord ParseState [tokens pos])

(defn- ps-peek  [{:keys [tokens pos]}] (get tokens pos))
(defn- ps-next  [{:keys [tokens pos] :as ps}] (assoc ps :pos (inc pos)))
(defn- ps-done? [{:keys [tokens pos]}] (>= pos (count tokens)))

(defn- expect!
  "Consume a token of given type; return [val updated-state] or throw."
  [type ps]
  (let [tok (ps-peek ps)]
    (if (and tok (= (:type tok) type))
      [(:val tok) (ps-next ps)]
      (throw (ex-info (str "Expected " type " but got " (:type tok) " '" (:val tok) "'")
                      {:expected type :got tok})))))

(defn- consume-if
  "If next token matches type, consume and return [true updated-state], else [false ps]."
  [type ps]
  (let [tok (ps-peek ps)]
    (if (and tok (= (:type tok) type))
      [true (ps-next ps)]
      [false ps])))

(defn- consume-val-if
  "Consume if next token matches type AND has value v."
  [type v ps]
  (let [tok (ps-peek ps)]
    (if (and tok (= (:type tok) type) (= (:val tok) v))
      [true (ps-next ps)]
      [false ps])))

;;; ═══════════════════════════════════════════════════════════════════════════
;;; Operator table (for Pratt parsing)
;;; ═══════════════════════════════════════════════════════════════════════════

(def ^:private op-table
  {":-"  {:prec 1200 :assoc :xfx}
   "?-"  {:prec 1200 :assoc :fx}
   ","   {:prec 1000 :assoc :xfy}
   ";"   {:prec 1100 :assoc :xfy}
   "->"  {:prec 1050 :assoc :xfy}
   "not" {:prec 900  :assoc :fy}
   "\\+" {:prec 900  :assoc :fy}
   "is"  {:prec 700  :assoc :xfx}
   "="   {:prec 700  :assoc :xfx}
   "\\=" {:prec 700  :assoc :xfx}
   "=="  {:prec 700  :assoc :xfx}
   "\\==" {:prec 700 :assoc :xfx}
   "=:=" {:prec 700  :assoc :xfx}
   "=\\=" {:prec 700 :assoc :xfx}
   "<"   {:prec 700  :assoc :xfx}
   ">"   {:prec 700  :assoc :xfx}
   "=<"  {:prec 700  :assoc :xfx}
   ">="  {:prec 700  :assoc :xfx}
   "@<"  {:prec 700  :assoc :xfx}
   "@>"  {:prec 700  :assoc :xfx}
   "@=<" {:prec 700  :assoc :xfx}
   "@>=" {:prec 700  :assoc :xfx}
   "+"   {:prec 500  :assoc :yfx}
   "-"   {:prec 500  :assoc :yfx}
   "*"   {:prec 400  :assoc :yfx}
   "/"   {:prec 400  :assoc :yfx}
   "//"  {:prec 400  :assoc :yfx}
   "rem" {:prec 400  :assoc :yfx}
   "mod" {:prec 400  :assoc :yfx}
   "**"  {:prec 200  :assoc :xfx}
   "^"   {:prec 200  :assoc :xfy}
   "|"   {:prec 1100 :assoc :xfy}})

(defn- infix-op? [tok]
  (and tok
       (contains? #{:op1 :op2 :atom} (:type tok))
       (let [v (:val tok)]
         (and (get op-table v)
              (#{:xfx :yfx :xfy} (:assoc (get op-table v)))))))

(defn- prefix-op? [tok]
  (and tok
       (= (:type tok) :atom)
       (let [v (:val tok)]
         (and (get op-table v)
              (#{:fx :fy} (:assoc (get op-table v)))))))

(defn- token-as-op [tok]
  (when (infix-op? tok) (:val tok)))

(defn- token-prec [tok]
  (when-let [v (and tok (:val tok))]
    (get-in op-table [v :prec] 0)))

;;; ═══════════════════════════════════════════════════════════════════════════
;;; Term parser (Pratt / operator-precedence)
;;; ═══════════════════════════════════════════════════════════════════════════

(declare parse-term parse-arg-list)

(defn- atom-token->term
  "Convert an atom-type token value string to a Clojure term."
  [v]
  (keyword v))

(defn- quoted-atom->term [s]
  ;; strip surrounding quotes
  (keyword (subs s 1 (dec (count s)))))

(defn- parse-list
  "Parse [...] list syntax. Returns [term ps]."
  [ps]
  (let [[_ ps1] (expect! :lbracket ps)]
    (let [tok (ps-peek ps1)]
      (cond
        ;; Empty list []
        (and tok (= (:type tok) :rbracket))
        [(keyword "[]") (ps-next ps1)]

        ;; Non-empty list
        :else
        (let [[head ps2] (parse-term 999 ps1)
              tok2 (ps-peek ps2)]
          (cond
            ;; [H|T]
            (and tok2 (or (= (:type tok2) :pipe)
                          (and (= (:type tok2) :op1) (= (:val tok2) "|"))))
            (let [ps3 (ps-next ps2)
                  [tail ps4] (parse-term 999 ps3)
                  [_ ps5] (expect! :rbracket ps4)]
              [{:op :cons :args [head tail]} ps5])

            ;; [H, ...] → build as cons list
            :else
            (let [[rest-items ps3]
                  (loop [items [head] ps' ps2]
                    (let [[got ps''] (consume-if :comma ps')]
                      (if got
                        (let [[item ps'''] (parse-term 999 ps'')]
                          (recur (conj items item) ps'''))
                        [items ps'])))
                  [_ ps4] (expect! :rbracket ps3)]
              ;; Build cons list from items
              [(reduce (fn [tail h] {:op :cons :args [h tail]})
                       (keyword "[]")
                       (reverse rest-items))
               ps4])))))))

(defn- parse-primary
  "Parse a primary term (atom, var, number, compound, list, parens)."
  [ps]
  (let [tok (ps-peek ps)]
    (when-not tok
      (throw (ex-info "Unexpected end of input" {})))
    (cond
      ;; Variable
      (= (:type tok) :var)
      [(:val tok) (ps-next ps)]

      ;; Float
      (= (:type tok) :float)
      [(Double/parseDouble (:val tok)) (ps-next ps)]

      ;; Integer
      (= (:type tok) :integer)
      [(Long/parseLong (:val tok)) (ps-next ps)]

      ;; Quoted atom
      (= (:type tok) :quoted-atom)
      [(quoted-atom->term (:val tok)) (ps-next ps)]

      ;; List
      (= (:type tok) :lbracket)
      (parse-list ps)

      ;; Parenthesized term
      (= (:type tok) :lparen)
      (let [ps1 (ps-next ps)
            [t ps2] (parse-term 1200 ps1)
            [_ ps3] (expect! :rparen ps2)]
        [t ps3])

      ;; Prefix operator (not, \+)
      (and (= (:type tok) :atom) (prefix-op? tok))
      (let [v   (:val tok)
            ps1 (ps-next ps)
            {:keys [prec assoc]} (get op-table v)
            rprec (if (= assoc :fy) prec (dec prec))
            [rhs ps2] (parse-term rprec ps1)]
        (cond
          (= v "not")
          [{:op :not :args [rhs]} ps2]
          (= v "\\+")
          [{:op :not :args [rhs]} ps2]
          :else
          [(term/make-compound v [rhs]) ps2]))

      ;; Atom (possibly followed by args)
      (= (:type tok) :atom)
      (let [v   (:val tok)
            ps1 (ps-next ps)
            tok2 (ps-peek ps1)]
        (if (and tok2 (= (:type tok2) :lparen))
          ;; Functor with args: p(...)
          (let [ps2 (ps-next ps1)
                [args ps3] (parse-arg-list ps2)
                [_ ps4] (expect! :rparen ps3)]
            [{:op (keyword v) :args args} ps4])
          ;; Plain atom
          [(keyword v) ps1]))

      ;; Negative sign (classical negation -p(X) treated as :- prefix)
      (= (:type tok) :neg-sign)
      (let [ps1 (ps-next ps)
            [inner ps2] (parse-primary ps1)]
        [{:op :- :args [inner]} ps2])

      ;; Operators used as atoms in some positions (like is, mod, rem)
      (contains? #{:op1 :op2} (:type tok))
      (let [v (:val tok)
            ps1 (ps-next ps)
            tok2 (ps-peek ps1)]
        (if (and tok2 (= (:type tok2) :lparen))
          (let [ps2 (ps-next ps1)
                [args ps3] (parse-arg-list ps2)
                [_ ps4] (expect! :rparen ps3)]
            [{:op (get term/op-str->kw v (keyword v)) :args args} ps4])
          [(get term/op-str->kw v (keyword v)) ps1]))

      :else
      (throw (ex-info (str "Unexpected token: " (:type tok) " '" (:val tok) "'") {:tok tok})))))

(defn- parse-arg-list
  "Parse comma-separated arguments until ')'. Returns [args ps]."
  [ps]
  (let [tok (ps-peek ps)]
    (if (and tok (= (:type tok) :rparen))
      [[] ps]
      (loop [args [] ps' ps]
        (let [[arg ps''] (parse-term 999 ps')]
          (let [[got ps'''] (consume-if :comma ps'')]
            (let [args' (conj args arg)]
              (if got
                (recur args' ps''')
                [args' ps'']))))))))

(defn parse-term
  "Parse a term with given minimum precedence (Pratt parser).
   Returns [term ps]."
  [min-prec ps]
  (let [[lhs ps1] (parse-primary ps)]
    (loop [lhs lhs ps' ps1]
      (let [tok (ps-peek ps')]
        (if (and tok (infix-op? tok)
                 (let [p (token-prec tok)]
                   (> p min-prec)))
          (let [v    (:val tok)
                {:keys [prec assoc]} (get op-table v)
                rprec (case assoc
                        :yfx (dec prec)
                        :xfy prec
                        :xfx (dec prec)
                        prec)
                ps1' (ps-next ps')
                [rhs ps2'] (parse-term rprec ps1')
                node (cond
                       (= v ",")  {:op :and :args [lhs rhs]}
                       (= v ";")  {:op :or  :args [lhs rhs]}
                       :else      {:op (get term/op-str->kw v (keyword v)) :args [lhs rhs]})]
            (recur node ps2'))
          [lhs ps'])))))

;;; ═══════════════════════════════════════════════════════════════════════════
;;; Rule / query parser
;;; ═══════════════════════════════════════════════════════════════════════════

(defn- goal-list
  "Flatten an :and tree into a flat list of goals."
  [t]
  (if (and (term/is-compound? t) (= (:op t) :and))
    (concat (goal-list (first (:args t))) (goal-list (second (:args t))))
    [t]))

(defn- parse-clause
  "Parse one clause (rule, fact, query, or directive) ending with '.'.
   Returns [clause-type clause ps] where clause-type is :rule/:query/:directive."
  [ps]
  (let [tok (ps-peek ps)]
    (cond
      ;; ?- query
      (and tok (= (:type tok) :op1) (= (:val tok) "?-"))
      (let [ps1 (ps-next ps)
            [body-t ps2] (parse-term 999 ps1)
            [_ ps3] (expect! :dot ps2)]
        [:query (vec (goal-list body-t)) ps3])

      ;; #directive
      (and tok (= (:type tok) :hash))
      (let [dir (:val tok)
            ps1 (ps-next ps)
            ;; parse rest of directive up to dot
            [arg ps2] (parse-term 999 ps1)
            [_ ps3] (expect! :dot ps2)]
        [:directive {:directive (subs dir 1) :arg arg} ps3])

      ;; :- body   (integrity constraint / headless rule)
      (and tok (= (:type tok) :op1) (= (:val tok) ":-"))
      (let [ps1 (ps-next ps)
            [body-t ps2] (parse-term 999 ps1)
            [_ ps3] (expect! :dot ps2)
            body (vec (goal-list body-t))
            head {:op :_false :args []}]
        [:rule (prog/make-rule head body) ps3])

      ;; Regular term (fact or rule)
      :else
      (let [[head-t ps1] (parse-term 999 ps)
            tok2 (ps-peek ps1)]
        (cond
          ;; head :- body.
          (and tok2 (= (:type tok2) :op1) (= (:val tok2) ":-"))
          (let [ps2 (ps-next ps1)
                [body-t ps3] (parse-term 999 ps2)
                [_ ps4] (expect! :dot ps3)
                body (vec (goal-list body-t))]
            [:rule (prog/make-rule head-t body) ps4])

          ;; fact
          (and tok2 (= (:type tok2) :dot))
          [:rule (prog/make-rule head-t []) (ps-next ps1)]

          :else
          (throw (ex-info "Expected ':-' or '.' after head" {:tok tok2})))))))

;;; ═══════════════════════════════════════════════════════════════════════════
;;; Program loader
;;; ═══════════════════════════════════════════════════════════════════════════

(defn parse-program
  "Parse a string containing a full s(CASP) program.
   Returns a program map (scasp.program)."
  [source]
  (let [tokens (tokenize source)
        ps0    (->ParseState (vec tokens) 0)]
    (loop [ps   ps0
           program (prog/new-program)]
      (if (ps-done? ps)
        program
        (let [[clause-type clause ps'] (parse-clause ps)]
          (case clause-type
            :rule
            (recur ps' (prog/assert-rule clause program))
            :query
            (recur ps' (prog/set-query clause program))
            :directive
            ;; For now, ignore directives (except #show / #abducible handled later)
            (recur ps' program)))))))

(defn parse-file
  "Load and parse a file, returning a program map."
  [path]
  (parse-program (slurp path)))
