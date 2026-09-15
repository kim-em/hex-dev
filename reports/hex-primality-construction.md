# Reusable Curve25519 certificates

The opt-in construction profile finds a checked certificate for `2^255 - 19`
with three non-leaf nodes, six table leaves, and eight factor entries. The
reference certificate in PR #10267 has five non-leaf nodes, six table leaves,
and ten entries. The generated certificate uses two cube-root nodes and takes
29 semantic search attempts without advancing `Rand.ofSeed n`.

The complete suggestion is pinned in
`conformance/HexPrimality/ConstructionConformance.lean`. Its replacement is
795 UTF-8 bytes, including whitespace. The applied proof in
`conformance/HexPrimality/Curve25519Replay.lean` imports `HexPrimality.Cert`
only. Both replay and full-tactic probe oleans are 7,568 bytes; the literal-only
probe olean is 4,736 bytes. These are whole-module artifact sizes, including
metadata, rather than serialized certificate sizes.

## Native work

The three new benchmark registrations are fixed mode-3 targets: one concrete
certificate shape and one required enumeration endpoint do not form a scaling
family. Each has five repeats, an expected result hash, and a five-second
operational deadline. The existing bit-size families remain registered.

| Operation | Inherited-affinity median | Pinned median | Pinned range |
|---|---:|---:|---:|
| Construction, including final compiled self-check | 722.681 ms | 1,771 ms | 1,156–2,216 ms |
| Compiled replay of the exact literal | 0.532 ms | 1.279 ms | 1.264–1.418 ms |
| `primesBelow 524289` | 253.860 ms | 573.519 ms | 569.619–612.063 ms |

The enumeration returns 43,390 primes, ending at 524287. The Lean stage-one
boundary test removes the table factors and the earlier factor 253947789517
from the 225-bit child's predecessor. Base two then reports `noFactor` at
262144 and factor 31757755568855353 at 524288. Each call counts one attempt
and preserves the supplied random state.

Both native runs are retained: the first used inherited host affinity, and
one follow-up used automatic CPU placement. All 30 completed repeat samples
appear in `hex-primality-construction-native-issue-10268.json` and
`hex-primality-construction-native-pinned-issue-10268.json` under
`reports/bench-results/`. The latter records its CPU placement. Host activity
is context, and does not reject any sample.

## Fresh-module phases and certificate comparison

`scripts/bench/primality_construction_sweep.py` measures seven adjacent pairs
in four blocks, alternating AB/BA order. It pins all arms to automatically
selected CPU 3 on the shared `chungus2` host, using Lean 4.34.0-rc2. The 56
completed samples, load observations, source hashes, source/olean sizes, build
output, and measured source hashes are retained in
`reports/bench-results/hex-primality-construction-issue-10268.json`.
The run overlaps ordinary repository builds; those observations remain in the
record. Each arm removes its own olean and runs `lake build`, with dependencies
prepared beforehand.

| Component pair | Arm medians | Median adjacent difference |
|---|---:|---:|
| Import baseline → input elaboration | 2.756 → 2.493 s | 0.103 s |
| Input → compiled certificate search | 2.542 → 3.495 s | 0.964 s |
| Input → certificate literal elaboration | 2.938 → 2.845 s | −0.114 s |
| Literal → literal elaboration and rendering | 3.396 → 3.002 s | −0.141 s |
| Literal → kernel replay | 3.376 → 16.469 s | 13.092 s |
| Import baseline → complete `primality?` | 3.406 → 18.002 s | 14.596 s |

The differences for input, literal, and rendering do not resolve their small
incremental costs above fresh-module and host variability. Negative differences
are retained observations, not negative execution costs. Search, replay, and
complete-invocation costs are separately visible. No quiet-host selection or
retry-until-clean procedure is used.

The separate adjacent certificate comparison uses the literal from PR #10267
as its reference, replayed through the same unchanged checker and toolchain:

| Block | Order | Reference | Generated |
|---|---|---:|---:|
| 0 | reference/generated | 19.654 s | 12.896 s |
| 1 | generated/reference | 29.852 s | 19.642 s |
| 2 | reference/generated | 45.358 s | 17.548 s |
| 3 | generated/reference | 10.856 s | 8.394 s |

The generated tree is smaller and replays faster in all four adjacent pairs.
These host-specific measurements support selecting it as the deterministic
fixture. The earlier 25-second observation in PR #10267 is contextual only.
The reference and generated replay modules occupy 1,021 and 1,189 source
bytes respectively; the generated source spells out constructor namespaces,
while the reference uses anonymous constructor notation. Both replay oleans
occupy 7,568 bytes.

## Replay attribution and checker choices

The checker is unchanged. A `samply record` capture of a fresh checker-only
literal build profiles kernel replay, rather than the much faster compiled
checker. Its busiest Lean worker contains 15,588 samples. The symbolized
summary and raw profile hash are in
`reports/bench-results/hex-primality-replay-profile-issue-10268.json`.
Inclusive kernel weak-head reduction appears in 85.74% of those samples;
allocation accounts for 62.55% of leaf samples. The profile is scoped to that
worker and is not a whole-process elapsed-time decomposition.

The executable checker exposes three relevant opportunities:

- **Repeated Fermat legs:** eight factor entries call `checkWitness`, hence
  eight Fermat exponentiations and eight reduced-exponent computations. There
  are only four distinct node/base pairs. Caching Fermat results by node/base
  could remove four repeated Fermat legs; any cache would need to preserve
  soundness for arbitrary input certificates.
- **Shared power ladders:** the 16 independent exponents have 2,376 binary
  squaring positions in total (`bitLength exponent - 1`). Taking one ladder
  per node/base would require 597 positions. This is arithmetic work counting,
  not a predicted kernel speedup: storing and reading a ladder adds terms and
  allocation, which the profile identifies as a substantial cost.
- **Unneeded children:** recursive subset selection removes two construction
  nodes and two factor entries from the reference shape. It checks table-based
  child-cost estimates before recursively certifying any candidate subset.
  This reduction already improves the paired replay measurements.

The smaller tree meets the construction and replay objective without changing
the checker representation. Grouped witnesses, Fermat caching, and shared
ladders require their own representation-level comparison before adoption;
the compiled arithmetic count alone does not establish their kernel cost.

## Reproduction

```sh
lake build HexPrimalityConstructionProbe hexprimality_bench
python3 scripts/bench/primality_construction_sweep.py --blocks 4 \
  --output /tmp/curve25519-phases.json
cpu=$(python3 scripts/bench/idle_core.py)
taskset -c "$cpu" .lake/build/bin/hexprimality_bench run \
  Hex.PrimalityBench.runConstruction Hex.PrimalityBench.runCurveChecker \
  Hex.PrimalityBench.runRuntimePrimes --export-file /tmp/curve25519-native.json
```

The ordinary tactic's budget and the ordinary integer-factorizer's 9999 smooth
ladder remain unchanged. Conformance covers those existing exact attempt and
random-state contracts alongside the new construction fixtures.
