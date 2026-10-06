# Nested normalization diagnostics

The captured source is `c7d917ccd3178db41014374244442f5716ed66fd`, tag
`issue-10378-nested-diagnostics-source-c7d917` (published on origin). It was
built on base `8bfb411d41310d75592bce84434c113d9f039888`, before integration on
`826a786e399881ca3718cb9c074fff680c1cc918`. Between those bases HexPoly,
HexSignDet, HexSturm and HexOrderedFn are unchanged. HexRealClosure changes
only BaseContext, BaseEmbedding, TowerCache, TowerInclusion, TowerTransport
and README; none belongs to this driver's import closure. The captured
source is retained by its tag even though rebase changed its ancestry.
`source-closure.json` records 149 reachable project files, all byte-identical
between that captured source and the integrated driver.
`build.json` records the ordinary
and diagnostic executable digests, generated C inputs, seven observed worker
entries, compiler recipes and link commands. The binaries and copied generated
C are retained at `/home/kim/.codex/tasks/hex-10378/nested-counts-aggregated/`.

Each level selects the unique root in `(0,1)` of
`(2X² − αₗ₋₁)(X − 3)`, with `α₀ = 1`. The original nonmonic cubic, root interval
and selected root remain fixed in both policies. Each arm constructs its own
validated descriptor evidence. The level-two root graph is 5073 bytes in the
clean arm and 991 bytes in the eager arm; the level-one graph is 627 bytes in
both. Packing uses these different lower-level representations and evidence,
so counts include their effect as well as the top-level policy. The workload computes
`(1 + α_d)^m / (α_d − 3)`.
Clean storage uses the actual zero-aware `ofPoly` packing. Eager storage reduces
against the monic working cubic and packs once per operation at every level.
Every defining head has leading coefficient 2, so production `canReduce` is
false and the clean arm retains unreduced nonzero polynomials. This workload
does not measure production reduction for monic heads with clean coefficients.
The ordinary Mathlib-free executable also checks value roundtrip and replays
all root descriptors and the actual final query graph.

The independent python-flint 0.9.0 oracle interprets every stored coefficient
in `Q(γ)`, `γ^(2^d) = 2`, with `αₗ = γ^(2^(d−l))/2`. It checks the defining
polynomials, exact final value and negative sign. Graph statistics check graph
structure; the Lean reader performs mathematical replay. The oracle's historical
`selected_root_sign_checked` key checks the negative sign under the specified
positive-root assignment in `Q(γ)`; it does not authenticate root selection.
The native descriptor replay supplies that root identity.

| Depth | Products | Policy | Polynomial gcd / xgcdLeft | Lean integer gcd | GMP integer gcd | Stored value bytes | Query evidence bytes (after counted region) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 2 | clean | 17 / 17 | 126319 | 126319 | 141 | 430847 |
| 2 | 2 | eager | 17 / 17 | 45071 | 45071 | 107 | 4958 |
| 2 | 4 | clean | 23 / 23 | 248512 | 248512 | 216 | 1106461 |
| 2 | 4 | eager | 23 / 23 | 82295 | 82295 | 125 | 7114 |
| 3 | 1 | eager | 547 / 547 | 2873125 | 2873125 | 492 | 14495 |
| 3 | 1 | clean | unavailable | unavailable | unavailable | unavailable | unavailable |

The traced counts binary's depth-three clean process exited 124 at its operational 600-second limit
before producing a functional row or the flushed workload-start marker. Thus
it did not enter the counted workload: construction/preparation, including
trace callback/string overhead, did not finish. This establishes no timeout
for ordinary untraced preparation. The timeout gives no measurement of the
subsequent product/division expression. Its empty outputs remain
in the archive. Every completed run is retained; no sample was discarded or
retried. There is no matched depth-three comparison.

Counters cover only the region between `NESTED BEGIN` and `NESTED END`, excluding
construction, final query construction and replay. They include packing's internal sign queries and the final
value hash; the separately reported final sign runs after the counted region.
Callback categories nest: division invokes multiplication and inversion,
and inversion invokes its gcd/extended-gcd sites. Do not sum these categories. The observer counts workers for `DensePoly.gcd`, `xgcd`, `xgcdLeft` and
`pseudoGcd`, and actual Lean/GMP gcd entry calls. It does not instrument
HexPolyFast's `*With` entry points; their activity is not bounded by these
polynomial counts. It also counts per-level arithmetic/zero callbacks. Lean and GMP
counts describe different layers and must not be added; the two counts are
identical in every completed run. Polynomial xgcd,
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
lake build hexrealclosure_nested_normalization
python3 scripts/bench/build_nested_normalization_counts.py /tmp/nested-counts
/tmp/nested-counts/nested-normalization-counts 2 2 clean trace
/tmp/nested-counts/nested-normalization-counts 2 2 eager trace
```

The counter builder leaves the ordinary Lake binary and generated sources
unchanged. The linker's `--wrap` support (lld in the recorded build) and the pinned Lean
runtime calling convention
are required. Callback aggregation suppresses diagnostic trace printing while
calling each original thunk once. Classification tests reject boxed/argument
forwarders and callee names in specialization suffixes.

Historical `build.json` did not digest every unreplaced link input. Its source,
generated-worker and binary bindings are retained as recorded; it cannot prove
the complete historical link closure by itself. The current builder requires
a clean source tree, builds and verifies the native target, and records every
object/archive argument on the link line for future captures. These updates do
not replace or re-run any retained diagnostic sample.

`checked-d2-m2.json`, `checked-d2-m4.json` and `checked-d3-m1.json` re-check
the retained rows/traces with oracle commit
`ba4635fabe468d71cb1a713db5515478ecfbb2bf`. These include actual operation
counters and reject empty count regions, mismatched depth/product counts and
imbalanced inverse/gcd sites. This postprocessing collects no new sample.
The workload-shape checks and archive digests bind the recorded trace pairing;
they do not authenticate a process against arbitrary replacement data.

The fresh build on `2c2faba6b7bfcba9e253432c9e7ea244d788e1ea` reproduced both
ordinary and diagnostic binaries byte-for-byte. `rebuild-2c2fab.json` records
all 153 object/archive link arguments; `rebuild-comparison.json` checks both
binary digests against the historical capture. Thus the `2c2fab` executable and original diagnostic observer agree exactly.
The later integration base `9caee6229f3b58e3829425a5101167e9f0ba361e` also changes
none of the 149 driver source-closure files; no new binary equivalence capture
is attributed to that later base. The rebuild and oracle source commits are
retained by published tags `issue-10378-nested-rebuild-source-2c2fab` and
`issue-10378-nested-oracle-source-ba4635`.
System libraries resolved through `-l` are not individually hashed; the full
binary digests and pinned toolchain remain the reproduction boundary.

Derived entries content-key their oracle script by SHA-256. The manifest links
the unchanged original rebuild record to its exact builder script, retained
as `builder-42e3701e.py` in this archive. The current builder also records its own digest. Commit names provide historical context;
these content keys survive rebase and squash merge. The CI regression replays
every current derived command and verifies all manifest file digests, the
retained oracle and rebuild builder keys. The exact `oracle-478fefcc.py` is
archived and used for historical replay; the live oracle is tested separately
by the current fixture tuple and mutation suite, so later oracle edits need
not change this archive. The run inventory
attributes the binary digest from `build.json` and reconstructs parameter/trace
arguments from the original parameter inventory and filenames. These identities
were not independently captured at each launch; the empty timeout files supply
no internal parameter identity. The outer launcher was not archived separately. Earlier
`d2-m2-oracle.json` and `nested-c7d917-*-oracle*.json` are retained older
postprocessing outputs; `checked-*.json` are the current verified results.

The rebuilt link recipe resolves `libnautyffi.a` into the sibling
`hex-dev-issue-10378-algebraic-bound` worktree. Its digest is recorded and both
complete binaries match, but the local clean-tree check does not cover that
sibling. Exact reproduction of this recorded link recipe requires that
retained external input; a fresh normal Lake build may resolve its own pinned
archive instead.
