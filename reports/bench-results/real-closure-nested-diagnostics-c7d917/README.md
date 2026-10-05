# Nested normalization diagnostics

The immutable source is `c7d917ccd3178db41014374244442f5716ed66fd`, tag
`issue-10378-nested-diagnostics-source-c7d917`. `build.json` records the ordinary
and diagnostic executable digests, generated C inputs, seven observed worker
entries, compiler recipes and link commands. The binaries and copied generated
C are retained at `/home/kim/.codex/tasks/hex-10378/nested-counts-aggregated/`.

Each level selects the unique root in `(0,1)` of
`(2X² − αₗ₋₁)(X − 3)`, with `α₀ = 1`. The original nonmonic cubic and descriptor
remain fixed in both policies. The workload computes `(1 + α_d)^m / (α_d − 3)`.
Clean storage uses the actual zero-aware `ofPoly` packing. Eager storage reduces
against the monic working cubic and packs once per operation at every level.
The ordinary Mathlib-free executable also checks value roundtrip and replays
all root descriptors and the actual final query graph.

The independent python-flint 0.9.0 oracle interprets every stored coefficient
in `Q(γ)`, `γ^(2^d) = 2`, with `αₗ = γ^(2^(d−l))/2`. It checks the defining
polynomials, exact final value and negative sign. Graph statistics check graph
structure; the Lean reader performs mathematical replay.

| Depth | Products | Policy | Polynomial gcd / xgcdLeft | Lean integer gcd | GMP integer gcd | Query graph bytes |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | 2 | clean | 17 / 17 | 126319 | 126319 | 430847 |
| 2 | 2 | eager | 17 / 17 | 45071 | 45071 | 4958 |
| 2 | 4 | clean | 23 / 23 | 248512 | 248512 | 1106461 |
| 2 | 4 | eager | 23 / 23 | 82295 | 82295 | 7114 |
| 3 | 1 | eager | 547 / 547 | 2873125 | 2873125 | see retained oracle output |
| 3 | 1 | clean | unavailable | unavailable | unavailable | unavailable |

The depth-three clean process exited 124 at its operational 600-second limit
before producing a functional row or workload marker. Its empty outputs remain
in the archive. Every completed run is retained; no sample was discarded or
retried. There is no matched depth-three comparison.

Counters cover only the region between `NESTED BEGIN` and `NESTED END`, excluding
construction, final query construction and replay. They include the workload's
final sign and hash. The observer counts actual polynomial gcd workers, actual
Lean/GMP gcd entry calls, and per-level arithmetic/zero callbacks. Lean and GMP
counts describe different layers and must not be added. Polynomial xgcd,
pseudo-gcd and GMP extended-gcd counts were zero in the completed runs. The
instrumented executable is used only for counts: no scientific timings or
asymptotic fit are derived from it. These diagnostics do not discharge Phase 4.

Reproduce the functional CI fixture with:

```sh
lake build hexrealclosure_nested_normalization
.lake/build/bin/hexrealclosure_nested_normalization
python3 scripts/oracle/real_closure_nested_normalization.py conformance-fixtures/HexRealClosure/nested-normalization.jsonl
```

At the tagged source, reproduce isolated counters with a new output directory:

```sh
python3 scripts/bench/build_nested_normalization_counts.py /tmp/nested-counts
/tmp/nested-counts/nested-normalization-counts 2 2 clean trace
/tmp/nested-counts/nested-normalization-counts 2 2 eager trace
```

The counter builder leaves the ordinary Lake binary and generated sources
unchanged. GNU linker wrapping and the pinned Lean runtime calling convention
are required. Callback aggregation suppresses diagnostic trace printing while
calling each original thunk once. Classification tests reject boxed/argument
forwarders and callee names in specialization suffixes.
