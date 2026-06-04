# scasp-clj — Implementation Plan

A ground-up Clojure reimplementation of s(CASP): a top-down, grounding-free
Answer Set Programming (ASP) solver under stable model semantics with constraints.

Reference implementations live in `refs/`:
- `refs/scasp/` — original Ciao Prolog source (~21K lines)
- `refs/core.logic/` — Clojure miniKanren implementation (architecture reference)

---

## Background & Key Concepts

### What is s(CASP)?

s(CASP) is a goal-directed interpreter for Answer Set Programs. Unlike most ASP
solvers (Clingo, DLV), it does NOT ground the program first. This means it can
handle programs over infinite domains, list terms, and symbolic variables. It
returns *partial answer sets* where unbound variables are described by their
constraints.

### Stable Model Semantics

For a program P and a candidate model M:
- A rule `h :- b1, ..., bn, not c1, ..., not cm` is satisfied if whenever all
  bi are in M and none of ci are in M, then h is in M.
- M is a *stable model* if it is the minimal model of the *Gelfond-Lifschitz
  reduct* of P w.r.t. M (roughly: the program with negative literals replaced
  by their truth values in M).

### Key Algorithm: s(ASP) / s(CASP) top-down evaluation

The algorithm avoids grounding by:
1. Compiling *dual rules* at load time: for each predicate `p`, generate
   `not_p` rules by negating each body goal.
2. Detecting *odd loops over negation* (OLON) and generating an *NMR check*
   that is appended to every query.
3. Using a *Coinductive Hypothesis Set* (CHS) during solving to:
   - Detect positive loops (fail)
   - Detect even loops with intervening negation (coinductive success)
   - Propagate constraints from negated CHS entries (constructive coinductive failure)
4. Solving goals top-down, threading (var-env, CHS) through each step.

---

## Source Code Map (refs/scasp/src/)

```
sasp/
  variables.pl     (~728 lines)  — explicit var struct + unification engine
  solve.pl         (~1496 lines) — core recursive solver
  chs.pl           (~761 lines)  — Coinductive Hypothesis Set
  comp_duals.pl    (~404 lines)  — dual rule compilation (load-time transform)
  nmr_check.pl     (~521 lines)  — OLON detection + NMR check generation
  call_graph.pl    (~240 lines)  — call graph for loop detection
  program.pl       (~351 lines)  — program database (assert/retract wrapper)
  common.pl        (~400 lines)  — shared predicates (predicate/3, negate_functor, etc.)
  tokenizer.pl     (~522 lines)  — lexer
  text_dcg.pl      (~880 lines)  — DCG parser for Prolog-syntax ASP programs
  io.pl            (~381 lines)  — file loading, directive handling
  output.pl        (~1460 lines) — answer set + justification printing
  variables.pl     (~728 lines)  — variable struct (also listed above)
  rbtrees.pl       (~1643 lines) — red-black tree library (use Clojure maps instead)
  options.pl       (~128 lines)  — CLI option flags

scasp.pl           (~1937 lines) — top-level: solve/4, main/1, forall, c_forall, DCC
scasp_io.pl        (~2303 lines) — extended I/O, directives, #show, #abducible, etc.
clp_disequality_rt.pl (~406 lines) — disequality constraint runtime (.\=.)
clp_clpq.pl        (~208 lines)  — CLP(Q/R) integration (rational arithmetic)

modules/
  scasp_event_calculus/  — Event Calculus on top of s(CASP)
  scasp_stratification/  — stratification analysis
  scasp_forgetting/      — predicate forgetting
```

---

## Architecture Overview

### Term Representation

```clojure
;; Atoms:     keywords  :foo, :bar
;; Variables: strings   "A", "B", "_"  (first non-_ char is uppercase = variable)
;; Compounds: maps       {:op :foo :args ["X" :bar]}
;; Lists:     Clojure    [:cons head tail] or just Clojure seqs
;; Numbers:   Clojure    42, 3.14, 2/3 (rationals)
```

### Variable Environment (replaces Prolog's native unification)

The sCASP solver does NOT use Prolog's native unification for program variables.
It carries an explicit `var-env` threaded through every call. This maps cleanly
to Clojure immutable data structures.

```clojure
;; var-env structure:
{:names  {var-name -> value-id}     ; "A" -> 7
 :values {value-id -> var-value}    ; 7 -> {:constraints #{5 :foo} :bindable? true :loop-var 0}
 :name-cnt  int                     ; counter for fresh variable names
 :id-cnt    int}                    ; counter for fresh value IDs

;; var-value is one of:
{:val v}                                  ; bound to v
{:constraints #{...} :bindable? bool :loop-var int}  ; unbound or constrained
;; loop-var: 0=normal, 1=succeeded non-ground in positive loop, -1=in forall (cannot become loop-var)
;; bindable?: false means further binding/constraining triggers failure (used in CHS entries)
```

Two variables "aliased" (unified together) share the same value-id. Binding one
binds both. This is the union-find insight already present in the Prolog code.

### Coinductive Hypothesis Set (CHS)

```clojure
;; CHS: map of functor -> list of entries
{"p/1" [{:args ["A"] :success? false :nmr? false}
        {:args [:foo]  :success? true  :nmr? false}]}

;; check-chs returns one of:
;; :coinductive-success  — exact match, success flag set
;; :coinductive-failure  — exact match of negation present
;; :not-present          — proceed with rule expansion
;; :positive-loop        — same call on stack without intervening negation
```

### Solver Return Type

Every `solve-*` function returns a **lazy sequence of result maps**:
```clojure
{:var-env  <updated var-env>
 :chs      <updated CHS>
 :just     <justification tree node>
 :even-loops [...]}
```

Backtracking = taking the next element of the lazy sequence.
Failure = empty sequence.

### Dual Rules

For each user predicate `p/n`, comp-duals produces rules for `not_p/n`.
The key transformation: for each clause of p, negate each body goal in turn,
keeping prior goals as context. Body-only variables get wrapped in `forall`.

```
p(X) :- q(X), r(X).
; becomes:
not_p(X) :- not_q(X).          ; clause 1: negate q
not_p(X) :- q(X), not_r(X).   ; clause 2: prior goals + negate r
```

For multiple clauses of p, `not_p` calls all the individual clause duals.

### NMR Check

For programs with odd loops over negation (e.g., `p :- not p`), the solver
needs additional consistency checks. These are generated at load time and
appended to every query as extra goals:

```
_nmr_check :- _chk1, _chk2, ...
```

Each sub-check ensures a constraint entailed by stable model semantics holds.

---

## Constraint Systems

### Disequality (\=) — REQUIRED from day 1

The core algorithm needs disequality to represent partial answer sets.
When a variable appears in an answer but is not fully bound, its "forbidden
values" are tracked as constraints on the var-env.

```clojure
;; "X \= 5" adds 5 to X's constraint set
;; "X = 5" checks 5 is not in X's constraint set before binding
;; CHS entries carry these constraints into coinductive checks
```

Relevant source: `refs/scasp/src/clp_disequality_rt.pl` (~406 lines).
This is ~400 lines of Prolog; estimate 300-500 lines of Clojure.

### CLP(Q/R) — DEFER to Phase 3

Needed only for programs using `.=.`, `.>.`, `.<.` etc. (rational arithmetic
with symbolic/non-ground variables). Relevant for temporal reasoning and
continuous-domain programs (Event Calculus benchmarks).

Options when we get there:
- Implement a simple rational interval constraint solver
- Delegate to JVM library (choco-solver, JaCoP)
- Wrap an external Prolog process for CLP queries

Most symbolic ASP programs (graph coloring, family trees, legal reasoning,
birds/Tweety, etc.) do NOT need CLP(Q/R).

---

## Implementation Phases

---

### PHASE 0 — Project Skeleton
**Goal**: Runnable Clojure project with namespaces laid out, test harness wired.

- [ ] `lein new` or `deps.edn` project, REPL-friendly
- [ ] Namespace skeleton:
  - `scasp.term`        — term representation + helpers
  - `scasp.vars`        — variable environment
  - `scasp.unify`       — unification + disequality
  - `scasp.program`     — program database (rules, queries)
  - `scasp.duals`       — dual rule compilation
  - `scasp.nmr`         — NMR check + call graph
  - `scasp.chs`         — Coinductive Hypothesis Set
  - `scasp.solver`      — core solve-goals engine
  - `scasp.parser`      — tokenizer + term parser
  - `scasp.output`      — answer set + justification printing
  - `scasp.main`        — CLI entry point
- [ ] Property-based test setup (test.check)
- [ ] Port the `examples/` from refs/scasp as integration test fixtures

---

### PHASE 1 — Term Representation + Variable Environment
**Reference**: `refs/scasp/src/sasp/variables.pl`
**Goal**: A correct, tested variable environment that can emulate Prolog unification.

- [ ] Define term types: atom, var, compound, number, list
- [ ] `is-var?` — first non-underscore uppercase char = variable
- [ ] Implement `var-env` as described above (names map + values map + counters)
- [ ] `new-var-env` — empty env with counters at 0
- [ ] `get-value-id` — look up a variable's value ID
- [ ] `var-value` — look up what a variable is bound/constrained to
- [ ] `update-var-value` — return new env with binding set
- [ ] `add-var-constraint` — add a forbidden value to a variable's constraint set
- [ ] `generate-unique-var` — fresh variable name + ID
- [ ] `get-unique-vars` — alpha-rename a rule's variables to fresh names (called
      before each rule expansion — prevents variable capture between rules)
- [ ] `body-vars` — variables appearing in rule body but not head (for forall)
- [ ] `variable-intersection` — vars non-ground in both ancestor and current call
      (used for even-loop detection)
- [ ] Tests: round-trip bind/lookup, aliasing (two vars same ID), constraint sets

---

### PHASE 2 — Unification Engine
**Reference**: `refs/scasp/src/sasp/solve.pl` lines 1064–1254 (`solve_unify`, `solve_dnunify`, etc.)
**Goal**: A complete structural unification that respects the var-env.

- [ ] `solve-unify` — unify two terms, return updated var-env or nil on failure
  - var-var: share value ID (union-find step)
  - var-nonvar: check constraints, bind
  - nonvar-var: symmetric
  - compound-compound: same functor+arity, recurse on args
  - atom-atom: must be identical
- [ ] `solve-dnunify` — disequality: add constraint or detect immediate failure
  - Both unbound: error (at least one must be ground)
  - One unbound: add constraint
  - Both atoms: must differ
  - Both compounds same functor: recurse (at least one arg pair must differ)
- [ ] `occurs-check` — optional, for occurs-check mode
- [ ] `solve-subunify` — recurse on arg lists
- [ ] Tests: all cases in solve_unify, especially var aliasing through multiple
      levels of indirection, constraint satisfaction

---

### PHASE 3 — Program Database
**Reference**: `refs/scasp/src/sasp/program.pl`, `common.pl`
**Goal**: In-memory program DB that dual compilation and the solver can query.

- [ ] Program = `{:rules {functor -> [rule]} :query goals :predicates #{functor} :nmr-check [goals]}`
- [ ] `rule` record: `{:head compound :body [goal]}`
- [ ] `predicate` — pack/unpack `functor/arity` strings
- [ ] `negate-functor` — `"p/1"` → `"not_p/1"` and vice versa
- [ ] `is-dual?` — functor starts with `not_`
- [ ] `assert-rule`, `retract-rule` — return new program (immutable)
- [ ] `defined-rule` — get all rules for a functor
- [ ] `reserved-prefix?` — `_chk`, `_nmr`, etc.
- [ ] Tests: insert, lookup, multiple clauses for same predicate

---

### PHASE 4 — Dual Rule Compilation
**Reference**: `refs/scasp/src/sasp/comp_duals.pl`
**Goal**: `compile-duals: program -> program` that adds `not_p` rules for each user predicate.

- [ ] `outer-dual-head` — create dual head with fresh variable args
- [ ] `abstract-structures` — replace compound head args with variables + unification goals
- [ ] `prep-args` — determine which head args to keep vs. replace with vars
- [ ] `comp-dual3` — for a single clause, produce one dual sub-clause per body goal
      (keep all prior goals + negate the current one)
- [ ] `comp-dual2` — handle body-only variables via `forall`
- [ ] `comp-dual` — outer dual: call all per-clause duals
- [ ] `comp-duals` — iterate over all predicates in program
- [ ] `dual-goal` — negate a single goal (flip operators, `not X` → `X`, `X` → `not X`)
- [ ] Tests: single-clause rules, multi-clause rules, rules with body-only vars,
      rules with compound head args, rules with no clauses (dual = fact)

Example to validate:
```
p(X) :- q(X), r(X).   =>   not_p(X) :- not_q(X).
                            not_p(X) :- q(X), not_r(X).
```

---

### PHASE 5 — Call Graph + NMR Check
**Reference**: `refs/scasp/src/sasp/call_graph.pl`, `nmr_check.pl`
**Goal**: `generate-nmr-check: program -> program` that appends OLON sub-checks.

- [ ] `build-call-graph` — map of `functor -> #{called-functors}` from rule bodies
- [ ] `find-loops` — SCCs in call graph (Tarjan or Kosaraju)
- [ ] `olon-rules` — rules participating in odd loops over negation
      (cycle exists where negation count is odd)
- [ ] `olon-chks` — generate sub-check predicates for each OLON rule
- [ ] `generate-nmr-check` — assemble `_nmr_check` goal list, add to program
- [ ] Tests: no-loop programs (NMR check is empty), simple `p :- not p` case,
      even loops (not OLON), nested OLONs

---

### PHASE 6 — Coinductive Hypothesis Set
**Reference**: `refs/scasp/src/sasp/chs.pl`
**Goal**: Complete CHS data structure with all check/add/remove operations.

- [ ] CHS representation: `{functor -> [entry]}` where entry = `{:args [...] :success? bool :nmr? bool}`
- [ ] `new-chs` — empty CHS
- [ ] `check-chs` — main entry point, returns one of `:not-present`, `:success`, `:failure`,
      `:positive-loop`, plus even-loop info
  - coinductive failure: negation exact-match in CHS → fail
  - constructive coinductive failure: negation unifies → constrain args, recurse
  - coinductive success (success flag set): exact match found
  - check-negations: walk call stack for intervening negations between current call and ancestor
- [ ] `exact-match` — strict: unbound only matches unbound with same constraints
- [ ] `add-to-chs` — insert entry (check for duplicate first), apply even-loop var substitutions
- [ ] `remove-from-chs` — remove specific entry
- [ ] `check-negations` — walk call stack, detect even loops and positive loops
- [ ] `match-neg` / `match-neg-test` — constraint propagation from CHS negation entries
- [ ] `replace-vars` — for CHS entries: replace non-loop vars with fresh copies
- [ ] Tests: coinductive success, coinductive failure, constructive failure with constraints,
      even loop detection, positive loop detection, call stack interaction

---

### PHASE 7 — Core Solver
**Reference**: `refs/scasp/src/sasp/solve.pl`
**Goal**: `solve-goals` returns a lazy sequence of `{:var-env :chs :just :even-loops}`.

This is the heart of the system. Implement in order:

- [ ] `solve-goals` — iterate through goal list, threading state, returning lazy-seq
- [ ] `solve-goal` — dispatch: forall / builtin / expression / predicate
- [ ] `solve-expression` — numeric/relational ops: `=`, `\=`, `is`, `=:=`, `>`, `<`, etc.
- [ ] `solve-subexpr` — evaluate arithmetic expressions to ground values
- [ ] `solve-predicate` — check CHS, dispatch to `expand-call`
- [ ] `expand-call` — handle CHS flags: coinductive success (return), not-present (expand rules)
- [ ] `expand-call2` — iterate through matching rules, unify head, recurse on body
- [ ] `get-unique-vars` inside expand-call2 — alpha-rename rule before each use
- [ ] `solve-forall` — universal quantification over a variable
  - solve once, check if var is still unbound (done), constrained (enumerate constraint values), or bound (fail)
- [ ] `substitute` — replace variable with value in a term (used by forall)
- [ ] `gen-sub-vars` / `get-sub-vars` / `remove-cycle-heads` — even loop variable handling
- [ ] Tests: simple queries, backtracking, loops, forall, even loops

---

### PHASE 8 — Parser
**Reference**: `refs/scasp/src/sasp/tokenizer.pl`, `text_dcg.pl`, `io.pl`
**Goal**: Parse sCASP/Prolog-syntax programs into the program data structure.

Input syntax:
```prolog
p(X) :- not q(X).          % rule
q(X) :- not p(X).
?- p(A).                    % query
#show p/1.                  % directive
#abducible ab/1.
:- constraint_body.         % headless rule (integrity constraint)
```

- [ ] Tokenizer: atoms, variables (uppercase/underscore), numbers, operators, punctuation
- [ ] Operator table: `:-`, `?-`, `not`, `is`, `=`, `\=`, `=:=`, `=\=`, `<`, `>`, `=<`, `>=`, `@<` etc.
- [ ] Term parser: atoms, compounds, lists `[H|T]`, operator expressions with precedence
- [ ] Rule parser: `head :- body.` and `?- query.`
- [ ] Directive parser: `#show`, `#abducible`, `#pred`, `#domain`, `#table`, `#false`
- [ ] Integration: load file → program data structure
- [ ] Tests: all example programs in refs/scasp/examples/ parse correctly

Use `instaparse` or hand-written recursive descent. The Prolog DCG grammar in
`text_dcg.pl` is the authoritative spec.

---

### PHASE 9 — Output + Justification Trees
**Reference**: `refs/scasp/src/sasp/output.pl`, `refs/scasp/src/scasp_io.pl`
**Goal**: Print answer sets and justification trees matching sCASP's format.

- [ ] `print-chs` — print the answer set (selected literals + their constraints)
- [ ] `print-vars` — print query variable bindings
- [ ] `format-term` — fill in variable values, strip internal prefixes (`_chk`, `not_`, etc.)
- [ ] `print-justification` — print the tree of rules + goals that justified the answer
- [ ] `print-abducibles` — list abducible atoms in the model
- [ ] Format modes: `--plain`, `--human`, `--long`, `--mid`, `--short`
- [ ] Tests: output matches sCASP reference output for example programs

---

### PHASE 10 — CLI + Integration Tests
**Goal**: A working `scasp` command that passes the reference test suite.

- [ ] CLI arg parsing: `-s0`, `-s5`, `--tree`, `--code`, `--human`, `--quiet`, etc.
- [ ] `main` entry: load file → compile duals → NMR check → run query → print results
- [ ] Interactive mode (`-i`): REPL loop reading queries
- [ ] Integration test runner: run all `refs/scasp/examples/*.pl` and diff output
      against reference (or against sCASP itself if installed)
- [ ] Test cases from `refs/scasp/test/`

---

### PHASE 11 — CLP(Q/R) Constraint Arithmetic
**Reference**: `refs/scasp/src/clp_clpq.pl`, `refs/scasp/src/clp_disequality_rt.pl`
**Goal**: Support `.=.`, `.>.`, `.<.`, `.>=.`, `.=<.`, `.<>.` operators for rational arithmetic.

Needed for:
- Event Calculus temporal programs (`T .>. 0`, `T2 .-. T1 .<. 35`)
- Yale shooting scenario
- Any program with symbolic numeric variables in answers

Options (decide at implementation time):
- [ ] Option A: Implement rational interval constraint store (Simplex-based)
- [ ] Option B: Delegate to choco-solver or JaCoP via interop
- [ ] Option C: Spawn a SWI-Prolog subprocess for CLP queries

Whichever option: the interface is `solve-clp-constraint(constraint, var-env) -> var-env | nil`.

---

### PHASE 12 — Advanced Features
**Goal**: Feature parity with the `scasp.pl` top-level.

- [ ] `c_forall/2` — constrained forall (experimental, see `refs/scasp/src/scasp.pl`)
- [ ] Dynamic Consistency Check (`--dcc`) — checks consistency of CHS on every step
- [ ] `#table` / tabling — memoize certain predicates
- [ ] `#abducible` — mark predicates as abducible (appear in answer even without rules)
- [ ] HTML justification output (`--html`)
- [ ] Timeout support (`--timeout`)
- [ ] `--forget` — predicate forgetting (refs/scasp/src/modules/scasp_forgetting/)
- [ ] Stratification analysis (refs/scasp/src/modules/scasp_stratification/)
- [ ] Event Calculus module (refs/scasp/src/modules/scasp_event_calculus/)

---

## Testing Strategy

### Unit tests (each phase)
Per-namespace unit tests. Test against known values derived from the Prolog
source comments and docstrings.

### Property-based tests (Phases 1–2)
Use `test.check` to verify unification properties:
- Idempotence: `unify(unify(t1, t2, env), t1, t2) = unify(t1, t2, env)`
- Symmetry: `unify(t1, t2) succeeds iff unify(t2, t1) succeeds`
- Var aliasing: if X=Y then binding X binds Y

### Integration tests (Phases 7+)
Run example programs through the solver and check answer sets. Golden outputs
can be generated by running `scasp` (if installed) or reading the expected
outputs from `refs/scasp/test/`.

Priority examples (increasing difficulty):
1. `tweety.pl` — basic default reasoning, no constraints
2. `graph-color-v2.pl` — classic ASP, integrity constraints
3. `1.family.pl` — recursive rules, negation
4. `blocks-world.pl` — planning
5. `benchmark_iclp18/towers_hanoi/` — loops, larger programs
6. Yale shooting scenario — needs CLP(Q/R)

---

## Key Invariants to Preserve

1. **Variable alpha-renaming**: Before expanding any rule, ALL variables in that
   rule must be renamed to fresh names. Failure to do this = variable capture =
   wrong answers.

2. **CHS remove-before-add pattern**: When expanding a call, the solver adds it
   to CHS with `success=false` first, expands, then REMOVES that entry and adds
   it back with `success=true`. If you skip the remove, stale entries corrupt the
   coinductive check.

3. **Even loop variable substitution**: When an even loop is detected, loop
   variables need to be replaced with fresh substitution variables in the CHS
   entry. This ensures future coinductive checks work correctly.

4. **NMR check placement**: The NMR check goals must be appended to the query
   (not prepended) and solved AFTER the user goals. The solver tracks `in-nmr?`
   to handle CHS entries added during NMR differently.

5. **Exact-match semantics**: CHS lookup uses "exact match" (unbound matches only
   unbound with identical constraints) for coinductive success, but looser
   unification for coinductive failure checks. These are different intentionally.

---

## Notes on core.logic as Reference

`refs/core.logic/` is useful for:
- How to structure a lazy-sequence-based logic engine in Clojure (look at `core.logic.protocols`)
- The `IUnifyTerms` / `IReifyTerm` protocol pattern for extensible term types
- How substitution environments (`Substitution`) are threaded through goals
- The `conde`/`fresh`/`run*` interface as inspiration for the REPL API

Key differences from core.logic:
- core.logic uses miniKanren's substitution model (persistent map of var→val)
- sCASP needs the richer var-env with constraint sets, bindability flags, loop-var flags
- sCASP's "CHS" has no miniKanren equivalent — it is specific to ASP coinduction
- core.logic doesn't do dual compilation or NMR checks (it's Prolog, not ASP)

---

## Estimated Timeline

| Phase | Effort |
|-------|--------|
| 0 — Skeleton | 1–2 days |
| 1 — Var env | 1–2 weeks |
| 2 — Unification | 1–2 weeks |
| 3 — Program DB | 3–5 days |
| 4 — Dual compilation | 1–2 weeks |
| 5 — NMR check | 1–2 weeks |
| 6 — CHS | 3–5 weeks |
| 7 — Core solver | 4–6 weeks |
| 8 — Parser | 1–2 weeks |
| 9 — Output | 1–2 weeks |
| 10 — CLI + integration | 1–2 weeks |
| 11 — CLP(Q/R) | 6–10 weeks |
| 12 — Advanced features | 4–8 weeks |
| **Core (phases 0–10)** | **~4–6 months** |
| **Full parity** | **~10–15 months** |
