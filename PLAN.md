# scasp-clj — Implementation Plan

A ground-up Clojure reimplementation of s(CASP): a top-down, grounding-free
Answer Set Programming (ASP) solver under stable model semantics with constraints.

No parser — programs are built programmatically as Clojure data (no .pl file support needed).

Reference implementations live in `refs/`:
- `refs/scasp/` — original Ciao Prolog source (~21K lines)
- `refs/core.logic/` — Clojure miniKanren implementation (architecture reference)

---

## Current Status — 2026-06-05

**31 tests, 59 assertions, 0 failures.**

Run with:
```
clj -X:test :nses '[scasp.vars-test scasp.unify-test scasp.solver-test scasp.main-test]'
```

### What works

| Area | Files | Tests |
|---|---|---|
| Term representation | `term.clj` | implicit |
| Variable environment (union-find, constraints, bindability, loop-var flags) | `vars.clj` | `vars-test.clj` (14 tests) |
| Unification + disequality (`solve-unify`, `solve-dnunify`) | `unify.clj` | `unify-test.clj` (9 tests) |
| Program database (`assert-rule`, `defined-rules`, `set-query`) | `program.clj` | implicit |
| Dual rule compilation (`compile-duals`, `comp-dual`) | `duals.clj` | implicit |
| NMR check generation (`generate-nmr-check`, OLON detection, Tarjan SCCs) | `nmr.clj` | implicit |
| CHS: positive-loop detection, even-loop detection, coinductive success/failure | `chs.clj` | `solver-test.clj` |
| CHS: even-loop var substitution (freeze non-loop vars before storing) | `chs.clj`, `vars.clj` | `main-test.clj` |
| Core solver: `solve-goals`, `solve-goal`, `expand-call`, `expand-call2` | `solver.clj` | `solver-test.clj` (7 tests) |
| Arithmetic/comparison builtins (`is`, `=:=`, `<`, `>`, `=<`, `>=`, `=\=`, `\=`) | `solver.clj` | `solver-test.clj` |
| `forall(V, Goal)` universal quantification | `solver.clj` | implicit |
| Integrity constraints (`_false/0` rules, `:- body.`) | `nmr.clj` | `main-test.clj` |
| NAF default reasoning, recursive rules | `solver.clj` | `solver-test.clj`, `main-test.clj` |
| Output + justification trees | `output.clj` | — |
| Programmatic API (`solve`, `solve-all`, `solve-n`, `build-program`) | `main.clj` | `main-test.clj` (6 tests) |

### Known working programs

- Tweety (NAF default reasoning with penguin/bird hierarchy)
- Family trees (recursive ancestor)
- OLON / self-referential NAF (`p :- not p`)
- Integrity constraints with ground bodies
- Even loops with variable substitution (`p(X) :- not q(X). q(X) :- not p(X).`)
- Arithmetic queries and disequality constraints

### Key invariants (do not break)

1. **Alpha-renaming**: `get-unique-vars` is called before every rule expansion in `expand-call2`. Never skip it.
2. **CHS remove-before-add**: `expand-call` adds `success=false`, expands all rules, then removes and re-adds `success=true`.
3. **`coinductive-failure?` only on `success? false`**: Fixed 2026-06-05. Triggers OLON coinductive success for the dual only when the positive is *currently being proved*, not when it previously completed.
4. **Call stack is newest-first**: `expand-call` uses `(into [{:goal goal}] call-stack)`. Fixed 2026-06-05. Using `conj` (appends) caused `check-negations` to see the oldest ancestor first and falsely detect positive loops before seeing intervening negations.
5. **Even-loop var substitution**: `add-to-chs` calls `replace-args-for-chs` to freeze non-loop vars before storing. Loop vars (by value-id in the even-loop cvars set) are kept live.
6. **`add-var-constraint` works on non-bindable vars**: Allows forall-generated vars to still accumulate disequality constraints (fixed — no `bindable?` guard).

---

## Architecture

### Term representation
```clojure
;; Atoms:     keywords       :foo, :bar
;; Variables: strings        "A", "X"  (first non-_ char uppercase = variable)
;; Compounds: maps           {:op :foo :args ["X" :bar]}
;; Numbers:   Clojure nums   42, 3.14
;; Lists:     compounds      {:op :cons :args [head tail]}, (keyword "[]") for nil
```

### Variable environment
```clojure
{:names  {var-name → initial-id}   ; "X" → 3
 :values {id → var-value}          ; 3 → {:constraints #{} :bindable? true :loop-var 0}
 :name-cnt int   ; counter for fresh names
 :id-cnt   int}  ; counter for fresh IDs

;; var-value is one of:
{:val v}                                             ; bound
{:constraints #{v1…} :bindable? bool :loop-var n}   ; unbound/constrained
{:link id}                                           ; union-find link
;; loop-var: 0=normal, 1=loop var, -1=forall var (cannot become loop var)
;; bindable? false = frozen (CHS entry var, forall domain var)
```

### CHS
```clojure
{"p/1" [{:args [term…] :success? bool :nmr? bool} …]}
;; check-chs returns lazy seq of {:result :not-present|:coinductive-success :var-env … :even-loop …}
;; empty seq = failure
```

### Solver result
```clojure
{:var-env … :chs … :just … :even-loops […]}
;; empty lazy seq = failure; backtracking = take next element
```

### Dual rule shape
```
p(X) :- q(X), r(X).
→  not_p(X) :- not_q(X).         ; negate q, nothing before it
   not_p(X) :- q(X), not_r(X).   ; keep q, negate r
```
Body-only variables (not in head) are wrapped with `forall`.

### NMR check
- OLON rules detected via Tarjan SCC on the call graph
- One `_chkN/0` sub-check per OLON rule, calling the dual of its head
- `_nmr_check/0 :- _chk1, _chk2, …` appended to every query
- Integrity constraints (`_false/0` rules): separate `_chk_0_N/0` sub-checks

---

## What's missing (prioritised)

### Priority 1 — DCC (Denial Consistency Check)
**Reference**: `refs/scasp/src/scasp.pl` lines 450–496
**Needed for**: integrity constraints with *variables* in the body (graph coloring style):
```
:- col(X,C), col(Y,C), edge(X,Y).   % X,Y,C are variables
```
Currently only ground-body integrity constraints work (the `_false/0` sub-checks via
`_chk_0_N` use forall, but the non-bindable forall vars can't unify with ground fact heads
when the constraint body uses variable predicates like `col(X,C)`).

The reference DCC mechanism:
- After the query succeeds, re-run each integrity constraint body with fresh vars
- If any constraint body succeeds (= constraint fires), the whole branch fails
- This is separate from the NMR check and runs as a post-processing step

Steps:
- [ ] In `nmr.clj` or `solver.clj`: add `run-dcc` function that iterates `_false/0` rules
- [ ] For each `_false/0` rule, solve its body against the current `var-env`/`chs`
- [ ] If any body succeeds → fail the branch (return empty seq)
- [ ] Wire `run-dcc` into `run-query` after the main query goals but before returning results
- [ ] Test: graph coloring `col(X,C) :- node(X), color(C), not diff_col(X,C).` with edge constraints

### Priority 2 — `#abducible` support
**Reference**: `refs/scasp/src/scasp_io.pl`
**Needed for**: abductive reasoning programs where some predicates have no rules

Steps:
- [ ] Add `:abducibles #{functor}` field to program map in `program.clj`
- [ ] Add `mark-abducible` and `abducible?` helpers to `program.clj`
- [ ] In `expand-call` (solver.clj): if functor is abducible and `(empty? rules)`, succeed with goal added to CHS
- [ ] In `build-program` (main.clj): accept optional `:abducibles` parameter
- [ ] Test: simple abductive program — `?- fly(X).` with `#abducible fly/1` and constraint `fly(X) :- bird(X).`

### Priority 3 — `solve-forall` edge cases
**Reference**: `refs/scasp/src/scasp.pl` `c_forall`

Currently `solve-forall` marks V non-bindable and checks for constraints afterward.
Edge cases not covered:
- [ ] Goal fails immediately → should succeed (vacuous truth: `forall(X, false)` succeeds when no X exists)
- [ ] Arithmetic constraints in the forall body (V accumulates numeric constraint set)
- [ ] Nested forall

### Priority 4 — `match-neg` / constraint propagation from CHS negations
**Reference**: `refs/scasp/src/sasp/chs.pl` `match_neg`, `match_neg_test`

When CHS has a negated entry (e.g. `not_p(X)` with `success=false`) and the current goal
is `p(Y)`, the constraints from `X` should be propagated to `Y`. Currently we only handle
the exact-match coinductive-success case, not the constraint-propagation case.

Steps:
- [ ] In `check-chs`: when `coinductive-failure?` triggers, propagate constraints from the
      matching CHS entry's args to the current call's args via disequality
- [ ] Test: program where constraint propagation is needed for a correct partial answer

### Priority 5 — CLP(Q/R) symbolic numeric constraints
**Reference**: `refs/scasp/src/clp_clpq.pl`
**Needed for**: programs with symbolic numeric answers (`X > 0, X < 10`)

Most programs using standard integer arithmetic work already (Prolog-style `is/2`, `>/2` etc.).
CLP(Q/R) is only needed when a variable appears *unground* in an answer with numeric bounds.

Options (decide at implementation time):
- A: Extend `var-value` `:constraints` to hold CLP predicates, check at binding time
- B: Delegate to a JVM constraint solver (choco-solver, JaCoP) via interop
- C: Simple interval/difference constraint store sufficient for most benchmarks

---

## Integration test coverage gaps

These programs from `refs/scasp/examples/` should work but aren't tested yet:
- [ ] Graph coloring (needs DCC)
- [ ] Yale shooting scenario (needs CLP(Q/R) or works with ground time points?)
- [ ] Bird/penguin/Tweety extended (works now — just not in the test suite as a reference comparison)
- [ ] Hamiltonian path (NAF + recursion — likely works)
- [ ] Event Calculus (needs CLP(Q/R))

---

## Source file map

| File | Lines | Role |
|---|---|---|
| `term.clj` | 220 | Term types, predicates, functor strings, pretty-printing |
| `vars.clj` | 312 | var-env, union-find, constraints, alpha-renaming, CHS var substitution |
| `unify.clj` | 174 | `solve-unify`, `solve-dnunify` |
| `program.clj` | 114 | Program map, rule indexing, query, NMR check, predicates |
| `duals.clj` | 202 | Dual rule compilation |
| `nmr.clj` | 168 | Tarjan SCCs, OLON detection, NMR + integrity sub-checks |
| `chs.clj` | 216 | CHS data structure, `check-chs`, `check-negations`, `add-to-chs` |
| `solver.clj` | 294 | Core solver, `solve-goals`, `expand-call`, builtins, `solve-forall` |
| `output.clj` | 169 | Answer set formatting, justification tree printing |
| `main.clj` | 93 | Public API: `solve`, `solve-all`, `solve-n`, `build-program`, `print-results` |
