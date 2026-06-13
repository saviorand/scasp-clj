# scasp-clj

A Clojure port of [s(CASP)](https://gitlab.software.imdea.org/ciao-lang/sCASP) — a top-down, goal-directed Answer Set Programming solver that works without grounding.

s(CASP) extends stable-model ASP with:
- Negation-as-failure (NAF) via constructive coinduction
- Strong (classical) negation
- Constraint Logic Programming over reals (CLP(R))
- Abductive reasoning
- Inductive learning via FOLD-R

Programs are represented as Clojure data structures — no Prolog parser is included.

## Installation

Add to your `deps.edn`:

```clojure
;; coming soon — clone and use as a local dep in the meantime
{:deps {scasp-clj/scasp-clj {:local/root "../scasp-clj"}}}
```

Requires Clojure 1.12+.

## Quick start

```clojure
(require '[scasp.main :as scasp]
         '[scasp.program :as prog])

;; Term helpers
(defn compound [op & args] {:op op :args (vec args)})
(defn rule [head & body]   (prog/make-rule head (vec body)))
(defn naf  [g]             {:op :not :args [g]})

;; Classic bird / penguin default-reasoning example
(def rules
  [(rule (compound :flies "X")  (compound :bird "X") (naf (compound :ab "X")))
   (rule (compound :ab "X")     (compound :penguin "X"))
   (rule (compound :bird "X")   (compound :penguin "X"))
   (rule (compound :bird :tweety))
   (rule (compound :penguin :sam))])

(scasp/solve-all rules [(compound :flies "X")])
;=> one result — X = :tweety  (sam is a penguin, so ab(sam) blocks flies(sam))
```

## Core API (`scasp.main`)

```clojure
;; Build + run in one step (returns lazy seq of result maps)
(scasp/solve rules query)
(scasp/solve rules query abducibles)          ; abducibles — set of functor strings e.g. #{"fly/1"}
(scasp/solve rules query abducibles opts)     ; opts — {:no-olon true, :no-nmr true}

;; Convenience wrappers
(scasp/solve-all rules query)                 ; eagerly collect all answers (may not terminate)
(scasp/solve-n n rules query)                 ; take at most n answers

;; Build a compiled program separately (useful for inspecting or reusing)
(scasp/build-program rules query)
(scasp/build-program rules query abducibles opts)

;; Extract variable bindings from a result
(scasp/result-bindings result ["X" "Y"])      ;=> {"X" :tweety, "Y" ...}

;; Print answers to stdout (Prolog style)
(scasp/print-results results query-goals)
```

Each result map contains:
- `:var-env` — variable bindings (pass to `scasp.vars/fill-in` or `result-bindings`)
- `:chs` — the Coinductive Hypothesis Set (selected literals in the answer set)
- `:just` — justification tree
- `:even-loops` — coinductive loop info

## Term representation

| Prolog | Clojure |
|--------|---------|
| `foo` (atom) | `:foo` (keyword) |
| `X` (variable) | `"X"` (string) |
| `42`, `3.14` | `42`, `3.14` |
| `f(X, a)` | `{:op :f :args ["X" :a]}` |
| `not p(X)` | `{:op :not :args [{:op :p :args ["X"]}]}` |
| `-p(X)` (strong neg) | `{:op :sneg :args [inner]}` |
| `[H\|T]` | `{:op :cons :args [H T]}` |
| `[]` | `(keyword "[]")` |

## Features

### Negation-as-failure

```clojure
;; p(X) :- bird(X), not ab(X).
(rule (compound :p "X") (compound :bird "X") (naf (compound :ab "X")))
```

### CLP(R) — constraint arithmetic

```clojure
;; Goals: X > 0, X < 10  →  X remains unbound with interval (0, 10)
(scasp/solve-all [] [(compound :> "X" 0) (compound :< "X" 10)])

;; Supported operators: < > =< >= =:= =\= .<. .>. .=<. .>=. .=. .<>. #< #> #=< #>= #= #<>
;; is/2 evaluates arithmetic: X is 2 + 3  →  X = 5
```

### Strong negation

```clojure
;; -flies(X) :- ab(X).   (classical/explicit negation)
(rule (prog/make-compound "-flies" ["X"]) (compound :ab "X"))
;; Consistency axiom :- flies(X), -flies(X). is added automatically.
```

### Abduction

```clojure
;; Mark a predicate as abducible — it can be assumed true with no rules
(scasp/solve-all rules [goal] #{"fly/1"})
```

### Induction (FOLD-R)

```clojure
(require '[scasp.inference :refer [inference]])

(inference :induction ontology :white)
;=> {:positive-rules [{white(X) :- from_s1(X)}]
;    :exception-rules []}
```

### Unified inference API (`scasp.inference`)

```clojure
(require '[scasp.inference :refer [inference print-justification]])

(doseq [r (inference ontology goal)]             ; deduction
  (print-justification r))

(doseq [r (inference :abduction ontology goal)]  ; abduction (open predicates auto-detected)
  (print-justification r))

(inference :induction ontology :target-predicate) ; induction via FOLD-R
```

## Semantics & divergence from upstream

This engine targets the same semantics as Ciao/SWI s(CASP), but a few points differ. Reference behavior was checked empirically against **SWI s(CASP) 1.1.4** and the Ciao algorithm variants.

- **Constructive negation over existentials follows Ciao's *sound* `forall`, not SWI's default.** SWI's default (`scasp_forall=all`) is **unsound** on `not p` where `p` is a rule with multiple existential body variables. Only Ciao's `--prev_forall` / `--sasp_forall` are sound there. This engine matches the **sound** behavior — on such programs our answer set can differ from what the default SWI CLI prints, intentionally.

- **No vacuous-truth `forall`.** `forall(V, G)` fails if `G` has no solution with `V` free. Matches Ciao `solve_forall`.

- **Negation of an undefined predicate succeeds.** An undefined `q` never holds (completion), so `not q(X)` holds universally. Matches s(CASP).

- **No Prolog parser (yet).** Programs are built as Clojure data structures.

## Performance

The solver uses **first-argument clause indexing**, so query cost does not grow with knowledge base size — only with the work the proof actually does.

| Phase | Cost | Notes |
|---|---|---|
| **Build** (`build-program`) | linear, ≈ 3.5 µs/fact | One-time; dominated by dual generation. |
| **Solve** (per query) | independent of KB size | First-argument indexing prunes non-matching clauses. |

Measured on a single-predicate fact base (Apple M-series, JVM):

| Facts | Build | Solve |
|------:|------:|------:|
| 10k | ~90 ms | 0.2 ms |
| 100k | ~0.5 s | 0.3 ms |
| 1M | ~3.5 s | 0.2 ms |

- **Large fact bases queried positively scale well** — ground/indexed lookups are effectively O(1).
- **Compilation is the upfront tax.** Build once, run many queries against it.
- **Deep recursion is the current limit.** Loop detection scans the call stack per call, making recursive proofs roughly O(depth²).

Benchmark harness: `bench/bench.clj`, `bench/bigbuild.clj` —
`clj -Sdeps '{:paths ["src" "resources" "bench"]}' -M -m bench`.

## Running the tests

```
clj -X:test
```

## Known limitations

- **No Prolog parser.** Programs must be constructed as Clojure data. A parser is the next major addition.
- **CLP(R) propagation across rule boundaries is incomplete.** Constraints like `X > Y` stored on `X` do not automatically re-fire when `Y` is bound by a later rule body goal.
- **`not(Comparison)` with an unbound variable is not handled.** `not(X > 3)` with unbound `X` should add `X =< 3` as a CLP constraint but currently fails. Use the flipped form instead: `X =< 3`.
- **`\=` (disequality) requires at least one ground argument.** Both-unbound `X \= Y` throws rather than deferring.

## Architecture

| File | Role |
|------|------|
| `term.clj` | Term types, operator table, pretty-printing |
| `vars.clj` | Variable environment (union-find, CLP(R) numeric bounds, relational constraint store) |
| `unify.clj` | Structural unification and disequality |
| `program.clj` | In-memory program database, rule indexing, abducibles |
| `duals.clj` | Dual rule compilation (NAF semantics without grounding) |
| `nmr.clj` | OLON detection (path-based DFS), NMR sub-check generation |
| `chs.clj` | Coinductive Hypothesis Set — loop detection, coinductive success/failure |
| `solver.clj` | Core solver, CLP(R) dispatch, `findall/3`, `call/N`, `forall/2`, DCC |
| `output.clj` | Answer set formatting, justification trees |
| `main.clj` | Public API |
| `inference.clj` | Unified deduction / abduction / induction API |
| `fold.clj` | FOLD-R inductive logic programming |

See [DESIGN.md](DESIGN.md) for internal architecture and invariants.

## License

MIT
