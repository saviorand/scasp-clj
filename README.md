# scasp-clj

A Clojure reimplementation of s(CASP): a top-down, grounding-free Answer Set
Programming solver under stable model semantics with constraints. Programs are
built as Clojure data structures (no parser). See [PLAN.md](PLAN.md) for the
architecture and implementation status.

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
