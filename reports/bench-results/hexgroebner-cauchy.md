# Packed Macaulay elimination

The current scalar prime-field kernels over `p = 65537` have source fingerprint
`892c46e6e126`. They were measured on the shared `chungus2` host with Lean
`v4.35.0-rc3`, one automatically leased CPU and three trial-major outer trials.
Input preparation is excluded; validation, workspace allocation, elimination,
output decoding and structural hashing are included. These are matrix kernels,
without polynomial symbolic preprocessing or full F4 computation.

| n | Hilbert, no provenance | Hilbert, with provenance | Clustered sparse | Spread sparse |
| --- | ---: | ---: | ---: | ---: |
| 32 | 0.300 ms | 0.347 ms | 0.205 ms | 3.144 ms |
| 64 | 1.684 ms | 1.897 ms | 0.410 ms | 12.015 ms |
| 128 | 10.978 ms | 12.616 ms | 0.826 ms | 46.533 ms |
| 256 | 79.181 ms | 84.765 ms | 1.652 ms | 180.635 ms |

Values are medians of all three completed samples per size, including samples
below the harness signal floor. The [raw export](hexgroebner-cauchy-892c46e6e126.json),
[source manifest](hexgroebner-cauchy-892c46e6e126.manifest),
[host/command metadata](hexgroebner-cauchy-892c46e6e126.measurement.json) and
[complete output](hexgroebner-cauchy-892c46e6e126.log) retain all 48 samples,
variability, hashes, memory, floor flags and the harness exit code.
No completed sample is discarded because of host activity. All matrix result
hashes agree across repetitions. Reported per-process RSS includes runtime and
prepared inputs; it is separate from the API's logical packed-payload counter.

The dense family consists of full-rank Hilbert matrices, a Cauchy special case,
with half the rows supplied as reducers. Its exact sparse update count is
`(n³ - n)/3`. Validation and scatter visit `n²` entries each, scans visit at
most `n²` positions, and output extraction visits `n(n+1)/2` positions. Shared
provenance records and hashes quadratically many nodes, with amortized
constant-time insertion; generated C reads the node index before consuming the
trace array in its push. At `n = 256`, whole-call time divided by sparse update
count is approximately 14.2 ns without provenance. This is not an isolated
row-update measurement: validation, setup, inversion, decoding and hashing
remain included.

Both dense timing verdicts are **inconclusive**. Without provenance the
normalized residual slope is `β = -0.316`; with provenance only one dimension
has verdict-eligible samples, so the harness fits no slope. Nine of twelve
provenance-enabled samples fall below the harness signal floor. Quadratic
work predicts growth below the leading cubic law at finite sizes, but its
relative timing contributions have not been separately attributed. These
sweeps do not establish the declared dense asymptotic timing laws.

The clustered sparse family has `2*n` rows and `256*n` columns, with six
nonzeros per row, nonunit leading coefficients and overlapping reducer tails.
Targets duplicate the independent reducers and add zero rank. Direct sparse
reducer installation, bounded active-range scans and one final column scan
give linear source work on this family. The timing verdict is **consistent
with declared complexity**, `β = +0.004` over the registered domain.

The spread sparse family also has `2*n` rows and `256*n` columns, with only
three nonzeros per row, but each row reaches the last column. Each target
cancels in one update and then inspects the remaining active interval. Source
work is quadratic in `n`. The timing verdict is **consistent with declared
complexity**, `β = -0.051`. At `n = 256` the spread-support median is 180.635 ms
versus 1.652 ms for the clustered family. This is direct evidence of the
interval scan limitation; these distinct inputs are not an optimization ratio.
An independent conformance allowance also exercises both clustered and spread
supports over 100,000 columns.

The portable accessors still use checked byte operations and `Nat` indices.
Scalar work accounting and metadata allocation remain costs, and intervals
with widely separated nonzeros still inspect their internal gaps. Whole-word
native access, delayed reduction, SIMD, parallelism and attribution of constant
factors remain open. No library phase or performance milestone is claimed.

Retained observations for source fingerprints `e74aa3ed6fd5`, `71383709ad2f`
and `76b276ff26f8`
are in their matching `.json`, `.manifest`, `.measurement.json` and `.log` files.
The three-family `e74aa3ed6fd5` sweep retains 36 completed samples with
inconclusive verdicts. The `71383709ad2f` sweep has a cubic-model verdict of
inconclusive (`β = -0.262`); `76b276ff26f8` has no verdict-eligible rows at its
100 ms sampling target. Each of those retains twelve completed samples. These are different source/sampling observations,
not a paired before/after performance comparison.

There are no external comparator measurements or correctness-theorem timings.
The fastest-open-source and overall-fastest F4 gaps remain unmeasured under
[#10987](https://github.com/kim-em/hex-dev/issues/10987). Full F4, finite
extensions, complete basis verification and kernel soundness proofs remain
separate deliverables.
