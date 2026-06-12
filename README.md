# scasp-clj

A Clojure reimplementation of s(CASP): a top-down, grounding-free Answer Set
Programming solver under stable model semantics with constraints. Programs are
built as Clojure data structures (no parser). See [PLAN.md](PLAN.md) for the
architecture and implementation status.

## Semantics & divergence from upstream

This engine targets the same semantics as Ciao/SWI s(CASP) (top-down,
grounding-free, stable models with constraints), but a few points differ from
the reference implementations. Reference behavior below was checked empirically
against **SWI s(CASP) 1.1.4** and the Ciao algorithm variants.

- **Constructive negation over existentials follows Ciao's *sound* `forall`, not
  SWI's default.** s(CASP) ships multiple `forall` algorithms. SWI's default
  (`scasp_forall=all`, the constructive Arias et al. algorithm) is **unsound** on
  `not p` where `p` is a rule with multiple existential body variables — it
  admits models in which a derivable atom is treated as false. Only Ciao's older
  `--prev_forall` / `--sasp_forall` are sound there. This engine matches the
  **sound** behavior. Consequence: on such programs our answer set can differ
  from what the *default* SWI CLI prints — intentionally, in the sound direction.
  (Verified equal to Ciao `--sasp_forall` on the patterns we test; we don't claim
  full cross-program equivalence — there's no parser to run the upstream corpus.)

- **No vacuous-truth `forall`.** `forall(V, G)` fails if `G` has no solution with
  `V` free; `forall(V, p(V))` for a non-empty Herbrand universe where `p` holds
  for no `V` is **false**, not vacuously true. Matches Ciao `solve_forall`.

- **Negation of an undefined predicate succeeds.** An undefined `q` never holds
  (completion), so `not q(X)` holds universally — its generated dual is always
  true. Matches s(CASP).

- **No Prolog parser (yet).** Programs are built as Clojure data
  (`{:op :p :args [...]}`, keyword constants, string variables), not parsed from
  `.pl` text. This is structural, not a semantic difference, but it means the
  upstream `#include`/operator/syntax surface isn't available.

- **Known solver gaps** (not divergences, just unimplemented corners) are tracked
  in [PLAN.md](PLAN.md) — e.g. some CLP(R) constraint propagation across rule
  boundaries.

The detailed NAF/`forall` soundness fix log lives in [PLAN.md](PLAN.md).

## Performance

The solver uses **first-argument clause indexing** (mirroring the WAM indexing
SWI/Ciao get from the underlying Prolog engine), so query cost does not grow with
the size of the knowledge base — only with the work the proof actually does.

Two phases have distinct cost profiles:

| Phase | Cost | Notes |
|---|---|---|
| **Build** (`build-program`: dual + NMR compilation) | linear, ≈ 3.5 µs/fact | One-time per program; dominated by dual generation (one sub-dual per clause, as in Ciao). |
| **Solve** (per query) | independent of KB size | First-argument indexing prunes non-matching clauses. |

Measured on a single-predicate fact base (Apple M-series, JVM, query the last
fact):

| Facts | Build | Solve |
|------:|------:|------:|
| 10k | ~90 ms | 0.2 ms |
| 100k | ~0.5 s | 0.3 ms |
| 1M | ~3.5 s | 0.2 ms |

### What to expect on large knowledge bases

- **Large fact bases queried positively scale well.** Ground/indexed lookups are
  effectively O(1) in the number of facts — a 1M-fact KB answers a ground query in
  sub-millisecond solve time. The cost you pay is the one-time ~3.5 s compilation.
- **Compilation is the upfront tax.** Plan to build a program once and run many
  queries against it. If a large fact table is only ever queried positively (never
  under `not`), its dual rules are pure overhead — lazy/selective dual generation
  is the lever to cut that (not yet implemented).
- **Deep recursion is the current limit.** Recursive predicates (transitive
  closure, long chains) are roughly **O(depth²)** because coinductive loop
  detection scans the call stack / hypothesis set per call. This is independent of
  KB size but bounds how deep a single proof can go before it gets slow.

Benchmark harness: `bench/bench.clj`, `bench/bigbuild.clj` —
`clj -Sdeps '{:paths ["src" "resources" "bench"]}' -M -m bench`.
