# scasp-clj — Design Notes

## Term representation

All terms are plain Clojure values:

| Kind | Representation | Example |
|------|---------------|---------|
| Variable | `String` | `"X"`, `"_Foo"`, `"_"` |
| Atom | `Keyword` | `:foo`, `:bar` |
| Number | Clojure number | `42`, `3.14`, `2/3` |
| Compound | `{:op kw :args [...]}` | `{:op :f :args ["X" :a]}` |
| NAF goal | `{:op :not :args [inner]}` | |
| Strong neg | `{:op :sneg :args [inner]}` | |
| Forall | `{:op :forall :args [var goal]}` | |

Operator keywords map Prolog syntax to safe Clojure keywords (e.g. `\=` → `:ne`, `=\=` → `:arith-ne`, `/` → `:div`). The full table is in `term/op-str->kw`.

## Variable environment

`vars/var-env` is an explicit union-find structure:

```
{:names  {var-name → initial-id}    ; string → int
 :values {id       → var-value}      ; int    → map
 :name-cnt int
 :id-cnt   int}
```

A `var-value` is one of:

- `{:val v}` — bound to value `v`
- `{:constraints #{...} :numeric-bounds {...} :numeric-neq #{...} :var-constraints [...] :bindable? bool :loop-var n}` — unbound/constrained
- `{:link id}` — union-find alias

Key invariants:
- `var-value` always returns one of the above; never `nil`.
- Bound values never carry constraint fields.
- `add-var-constraint` works on non-bindable vars (forall vars still collect disequality constraints during body solving).
- `check-var-constraints` must be called at every numeric bind site.

## Solving pipeline

```
build-program
  └─ assert-rule* → compile-duals → generate-nmr-check

run-query
  └─ solve-goals → solve-goal → solve-predicate
                              → solve-expression (arithmetic/CLP(R))
                              → solve-forall
                              └─ expand-call → expand-call2 (rule unification)
  └─ run-dcc (post-solve integrity check)
```

### Dual compilation

For each user predicate `p/n`, `duals/comp-dual` generates `not_p/n` rules that implement NAF without grounding. Inner duals (`_not_p_N`) handle individual clauses; body-only variables are wrapped in `forall`.

### NMR check

Odd loops over negation (OLONs) are detected by path-based DFS on the user-only call graph, tracking negation parity (0/1/2 mod-2 counter, same as the reference `nmr_check.pl`). For each OLON rule, a `_chk_N` predicate is generated and wrapped in nested `forall`s.

### CHS (Coinductive Hypothesis Set)

```
{functor-str → [{:args [...] :success? bool :nmr? bool} ...]}
```

`check-chs` runs in order:
1. Call-stack loop detection: positive loop → hard failure; even loop → coinductive success.
2. Exact match of completed positive entry → coinductive success.
3. Dual in-progress (`success? false`) → coinductive success (constructive failure of dual).
4. Dual entries that unify (non-exact) → propagate disequality constraints, continue as `:not-present`.

Call stack is newest-first (prepend, not append); `expand-call` uses `(into [new-entry] call-stack)`.

### CLP(R)

Unbound numeric variables carry:
- `numeric-bounds` — interval `[lo, hi]` with open/closed flags
- `numeric-neq` — set of excluded values
- `var-constraints` — list of `{:op :< :rhs other-var}` relational constraints

Constraints are checked/propagated at bind time via `check-var-constraints`. Cross-rule propagation (waking watchers when `rhs` is bound) is not yet implemented.

## Key call-site invariants

1. `add-to-chs` returns `[entry chs ve]` (3-tuple) — always destructure as such.
2. `expand-call` prepends to call-stack: `(into [{:goal goal}] call-stack)`. Appending breaks loop detection.
3. DCC runs against the result's CHS with `:abducibles #{}` to prevent new abductions during the check.
4. `check-var-constraints` must be called from every path that binds a numeric value (`solve-unify` var→non-var, `unify-vars` var→bound and bound→var).
