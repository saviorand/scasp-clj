# scasp-clj — Handoff Plan

A ground-up Clojure reimplementation of s(CASP): a top-down, grounding-free
Answer Set Programming solver under stable model semantics with constraints.
No parser — programs are built as Clojure data structures.

Reference implementations live in `refs/`:
- `refs/scasp/` — original Ciao Prolog source
- `refs/scasp/examples/` — example programs (yale-shooting, wedding, bec, etc.)

Run tests:
```
clj -X:test :nses '[scasp.vars-test scasp.unify-test scasp.solver-test scasp.main-test scasp.clpr-test scasp.builtins-test]'
```
Current baseline: **88 tests, 177 assertions, 0 failures.**

---

## What is fully implemented

| Area | File(s) |
|---|---|
| Term representation, operator table | `term.clj` |
| Variable environment (union-find, bindability, loop-var flags) | `vars.clj` |
| Unification + disequality (`solve-unify`, `solve-dnunify`) | `unify.clj` |
| Dual rule compilation | `duals.clj` |
| NMR check generation (OLON detection via path-based DFS, forall-wrapped sub-checks) | `nmr.clj` |
| CHS: positive/negative loop detection, even-loop, coinductive success/failure | `chs.clj` |
| CHS: constraint propagation from negated CHS entries | `chs.clj` |
| Core solver: `solve-goals`, `expand-call`, abducibles, DCC post-solve check | `solver.clj` |
| `forall/2` universal quantification | `solver.clj` |
| `findall/3`, `call/1`, `call/N` (partial application) | `solver.clj` |
| `true/0`, `fail/0`, `false/0` | `solver.clj` |
| Integrity constraints (headless `:-`) checked by DCC | `solver.clj`, `program.clj` |
| Strong negation (`-p(X)`) with auto consistency constraints | `program.clj` |
| Arithmetic/comparison builtins: `is`, `=:=`, `=\=`, `<`, `>`, `=<`, `>=`, `\=` | `solver.clj` |
| CLP(R) symbolic: ground/unbound mixed, var-var relational store, bind-time propagation | `vars.clj`, `solver.clj`, `unify.clj` |
| CLP(R) operators: `.<. .>. .=<. .>=. .=. .<>. #< #> #=< #>= #= #<>` | `term.clj`, `solver.clj` |
| Dual negation of all CLP(R) operators | `duals.clj` |
| `is/2` deferred when RHS is a single unbound variable | `solver.clj` |
| Answer formatting, justification trees, numeric bounds display | `output.clj` |
| Public API: `solve`, `solve-all`, `solve-n`, `build-program` | `main.clj` |

---

## Key architectural invariants (do not break)

1. **`var-value`** returns `{:val v}` (bound) or `{:constraints #{} :numeric-bounds {:lo -Inf :hi +Inf :lo-open? bool :hi-open? bool} :numeric-neq #{} :var-constraints [{:op kw :rhs var-name}] :bindable? bool :loop-var n}` (unbound). Never add fields to bound struct.
2. **`add-var-constraint` works on non-bindable vars** — no `bindable?` guard. Forall vars still accumulate disequality constraints.
3. **`coinductive-failure?` only triggers on `success? false` CHS entries** — not on completed (`success? true`) entries.
4. **Call stack is newest-first**: `expand-call` uses `(into [{:goal goal}] call-stack)`. Using `conj` breaks loop detection.
5. **`add-to-chs` returns `[entry chs ve]` (3-tuple)** — always destructure as such.
6. **DCC runs against the result's CHS with abducibles stripped** — prevents new abductions during the consistency check.
7. **`check-var-constraints`** is called at bind time in both `unify-vars` (var-var and var-bound paths) and `solve-unify` (var→non-var path). Any new bind path must also call it for numeric values.

---

## Discrepancy resolution log (as of 2026-06-06)

All three bugs identified in the comparison against `refs/scasp/src/sasp/` have been resolved. **83 tests, 168 assertions, 0 failures.**

### Bug A — `forall/2` constraint iteration ✅ Fixed

**Was:** Iterated over `(:constraints cur-cs)` (all disequality constraints), re-testing Goal for values V cannot take rather than values newly forbidden. Also lacked the vacuous-truth case when Goal has no solutions at all.

**Fix (`solver.clj:solve-forall`):** Added vacuous-truth path when `body-results` is empty. For the constrained path, now uses `set/difference` to find *newly acquired* constraints (not all constraints) and re-verifies Goal only for those new values.

---

### Bug B — Constructive coinductive failure via dual unification ✅ Fixed

**Was:** `check-chs` used a `dual-exact-match?` hard-fail clause that blocked `p` from getting coinductive success when `not_p` was in-progress in CHS (breaking OLON). The constructive path (`dual-entries-for-args`) existed but was wired incorrectly.

**Fix (`chs.clj:check-chs`):** Replaced `dual-exact-match?` with `coinductive-failure?` (checks `success? false` entries only) → coinductive success when dual is in-progress. Added `propagate-neg-constraints` to propagate disequality constraints from the dual entry. Kept `dual-entries-for-args` + `propagate-dual-constraints` for the constructive (non-exact-match) path.

---

### Bug C — OLON detection algorithm ✅ Fixed

**Was:** Tarjan SCC on the full compiled program (including dual `not_*` rules), detecting both `p/0 :- not p` AND the generated dual `not_p/0` as OLON participants, generating duplicate NMR sub-checks.

**Fix (`nmr.clj`):** Rewrote to use user-only call graph and path-based DFS with negation parity counting (mirrors `nmr_check.pl`). Added `user-functor?` filter, `build-user-call-graph`, `update-neg` (0/1/2 parity), `dfs-from` path-tracing DFS. Now correctly finds only the original user rule as the OLON participant.

---

### Minor — `no_olon` / `no_nmr` config flags ✅ Fixed

Added as an `opts` map to `build-program` / `solve` / `solve-all` / `solve-n`:
- `:no-nmr true` — skip NMR check entirely (no `_nmr_check` goals appended to query)
- `:no-olon true` — skip OLON detection; treat program as having no OLONs (generates trivial `_nmr_check` fact)

Usage: `(main/solve-all rules query #{} {:no-nmr true})`

---

## NAF soundness fixes (as of 2026-06-12)

Four `forall`/NAF soundness bugs fixed; constructive negation over rules with
existential body variables is now sound, including the multiple-existential case.
Reference behavior was checked empirically against SWI s(CASP) 1.1.4 (both as a
leak-detector and to confirm no valid `not`-successes were lost).

**Background — how the references differ.** s(CASP) has several `forall`
algorithms. SWI's *default* (`scasp_forall=all`, the constructive Arias et al.
algorithm) is **unsound** on duals with multiple existential body variables — it
leaks `not p` where `p` is derivable. Only the older Ciao algorithms
(`--prev_forall` / `--sasp_forall`) are sound on that pattern. This port's
`solve-forall` mirrors the Ciao `solve_forall/2/3` family (the sound one), and
now reproduces its answers on the patterns tested.

### Fixed — unsound vacuous-truth in `solve-forall` (`solver.clj`)

`forall(V, Goal)` froze `V`, solved `Goal` once, and on **no** solution returned
*success* ("vacuous truth"). That is unsound: `forall(V, p(V))` for a defined `p`
that simply can't unify `V` with a witness (e.g. `forall(V, claims(cA,V))`)
wrongly succeeded. SWI/Ciao give **no model** here under every algorithm. Fixed:
empty body-results → the forall **fails** (mirrors Ciao `solve_forall`).

### Fixed — duals for called-but-undefined predicates (`duals.clj`)

`compile-duals` only generated duals for *head* predicates. A predicate called
(in a body, or under `not`) but never defined had no `not_q` dual, so `not q(X)`
**failed** instead of succeeding universally (an undefined `q` never holds, so
`not q` always holds — confirmed against SWI). `compile-duals` now also feeds
called-but-undefined functors (collected via `goal-predicate-functors`) through
the existing empty-rules path, which emits `not_q` as a fact. This is also what
the old vacuous-truth branch was masking — the two fixes are complementary.

### Fixed — `forall` re-verification threading (`solver.clj`)

When re-verifying `forall(V, G)` for each value `V` excludes, the body may hold
only by constraining ANOTHER (outer) universally-quantified variable. The old
re-verify discarded the var-env, dropping those constraints, so a nested
`forall` over multiple existentials leaked. `solve-forall3` now threads the
var-env across values (so outer-var constraints accumulate) while keeping the
CHS independent per value (a sibling value's success entries must not grant
spurious coinductive success).

### Fixed — `forall` variable freshening (`solver.clj`)

`solve-forall` now alpha-renames the universal variable `V` (and its occurrences
in `Goal`) to a fresh name on entry — mirroring `my_copy_term(Var, Goal, …)` in
solve.pl. This was the root cause of the multi-existential leak: a nested forall
reusing the same source variable name (e.g. the inner `S1` of a re-verify)
inherited residual disequality constraints left in the var-env by an earlier
forall over that name, so its "new constraints" set came out empty and it
wrongly reported universal success.

Together these make the motivating pattern sound:
`overridden(E,A) :- claims(E,S1,A), claims(E,S2,B), outranks(B,A)` with
`authoritative(E,S) :- claims(E,S,A), not overridden(E,A)` now yields only the
highest-authority source (matches Ciao `--sasp_forall`). Covered by
`naf-multi-existential-test` and `naf-single-existential-test`.

---

## Three remaining solver gaps (no parser needed)

### Gap 1 — `is/2` with compound unbound RHS ✅ Fixed

`resolve-arith` now returns `[::linear coeff var offset]` for affine expressions with one unbound variable. The `:is` handler in `solve-expression` calls `vars/add-linear-eq` which:
- If LHS or RHS is already ground, derives and binds the other immediately.
- If both are unbound, stores `{:op :linear-eq :coeff c :rhs Y :offset k}` on X and the inverse on Y; `check-var-constraints` fires the derivation when either is later bound.

Handles: `X is Y + 1`, `X is 2 * Y`, `X is 3 - Y`, chains like `X is Y + 1, Y is 4 → X = 5`, and failure when the constraint is violated. Nonlinear expressions (e.g. `X is Y * Y`) still soft-fail as before.

---

### Gap 2 — CLP(R) propagation across rule boundaries

**Symptom:** `p(X) :- X > Y, q(Y). q(5).` — after `q(Y)` binds `Y=5`, the constraint `X > Y` (stored on `X` as `{:op :> :rhs "Y"}`) does not fire because `update-var-value` in `vars.clj` does not wake up watchers.

**Location:** `vars.clj` `update-var-value` (~line 128). Currently:
```clojure
(defn update-var-value [var-name val ve]
  (if-let [id (get-value-id var-name ve)]
    (assoc-in ve [:values id] val)
    ...))
```

**Fix:** After storing `{:val n}` for a numeric value, scan all values in `ve` for any `:var-constraints` entry whose `:rhs` equals `var-name`, and call `add-numeric-bound` on the watcher. Because `update-var-value` currently can't return `nil` (failure), introduce a `bind-numeric-var` helper that returns `ve | nil` and is used from all bind sites that set a numeric value.

**Key complication:** `update-var-value` is used for both numeric and non-numeric binds, and for frozen/non-bindable vars (CHS storage). Only propagate when the new value is `{:val n}` with `(number? n)` and the watcher var is still unbound.

**Test to write:**
```clojure
;; rules: p(X) :- X .>. Y, q(Y).   q(5).
;; ?- p(X).  →  X unbound with lo=5 open
;; ?- p(X), X is 6.  →  succeeds
;; ?- p(X), X is 3.  →  fails
```

---

### Gap 3 — `not(comparison)` when variable is unbound

**Symptom:** `not(X > 3)` when `X` is unbound routes to `solve-predicate` (finds no rule for `>/2`), returns no solutions. Should add `X =< 3` as a CLP(R) constraint.

**Location 1:** `term.clj` `is-expr?` (~line 176). Currently catches `not(is(...))` but not `not(comparison(...))`. Extend:
```clojure
(defn is-expr? [t]
  (or (comparison-op? t)
      (arith-expr? t)
      (and (is-compound? t) (= (:op t) :not)
           (let [inner (first (:args t))]
             (and (is-compound? inner)
                  (or (= (:op inner) :is)
                      (contains? comparison-ops (:op inner))))))))
```

**Location 2:** `solver.clj` `solve-expression` `:not` case. Add after the existing `not(is(...))` clause:
```clojure
;; not(Comparison) with unbound var → flip and add as CLP constraint
(and (= op :not)
     (let [inner (first args)]
       (and (term/is-compound? inner)
            (contains? comparison-ops (:op inner)))))
(let [inner (first args)
      flipped (duals/dual-goal inner)]
  (solve-clp-constraint (:op flipped) (first (:args inner)) (second (:args inner)) ve))
```

**Test to write:**
```clojure
;; not(X > 3) with X unbound  →  X gets hi=3 closed (X =< 3)
;; not(X > 3), X is 2  →  succeeds
;; not(X > 3), X is 5  →  fails
;; not(X > 3), not(X < 1)  →  X in [1,3]
```

---

## After the three gaps: the parser

The parser maps Prolog text → Clojure term representation:
- Variables: strings (`"X"`, `"_Foo"`)
- Atoms: keywords (`:foo`)
- Numbers: Clojure numbers
- Compounds: `{:op :keyword :args [...]}`
- Operator mapping: `term/op-str->kw` already has all operators including CLP(R) ones

Entry point: `(parse-program string)` → `{:rules [...] :query [...]}` passable to `main/build-program`.

Suggested approach: hand-written recursive-descent Prolog tokenizer/parser, or instaparse with a Prolog operator-precedence grammar. The operator precedence table needs: `:-`, `?-`, `,`, `;`, `not`/`\+`, `=`, `\=`, `is`, `=:=`, `=\=`, `<`, `>`, `=<`, `>=`, `+`, `-`, `*`, `/`, `//`, `mod`, `rem`, `**`, `^`, plus the CLP(R) dotted operators.

Special syntax to handle:
- `#abducible p/1` → call `prog/mark-abducible`
- `#include 'file.pl'` → load and merge (for BEC/yale-shooting)
- `:- body.` (headless) → integrity constraint, head is `{:op :_false :args []}`
- `-p(X)` (strong negation prefix) → `{:op :sneg :args [{:op :p :args ["X"]}]}`
- List syntax: `[H|T]` → `{:op :cons :args [H T]}`, `[]` → `(keyword "[]")`

---

## Source file map (current)

| File | Lines | Role |
|---|---|---|
| `term.clj` | 261 | Term types, operator table, `is-expr?`, pretty-printing |
| `vars.clj` | 461 | var-env, union-find, numeric bounds, relational constraint store, CHS var substitution |
| `unify.clj` | 178 | `solve-unify` (with numeric/relational checks), `solve-dnunify` |
| `program.clj` | 151 | Program map, rule indexing, builtins registry, abducibles |
| `duals.clj` | 220 | Dual rule compilation, `dual-goal` (including CLP(R) op flipping) |
| `nmr.clj` | 133 | Tarjan SCCs, OLON detection, NMR sub-check generation |
| `chs.clj` | 247 | CHS data structure, `check-chs`, `check-negations`, constraint propagation |
| `solver.clj` | 461 | Core solver, CLP(R) constraint dispatch, `findall/3`, `call/N`, `forall/2` |
| `output.clj` | 183 | Answer set formatting, numeric bounds display, justification trees |
| `main.clj` | 97 | Public API: `solve`, `solve-all`, `build-program`, `print-results` |
