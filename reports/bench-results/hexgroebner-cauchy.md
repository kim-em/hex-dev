# Packed Macaulay elimination

The current scalar prime-field kernels over `p = 65537` have source fingerprint
`e74aa3ed6fd5`. They were measured on the shared `chungus2` host with Lean
`v4.35.0-rc3`, one automatically leased CPU and three trial-major outer trials.
Input preparation is excluded; validation, workspace allocation, elimination,
output decoding and structural hashing are included. These are matrix kernels,
without polynomial symbolic preprocessing or full F4 computation.

| n | Hilbert, no provenance | Hilbert, with provenance | Sparse rectangular |
| --- | ---: | ---: | ---: |
| 32 | 0.294 ms | 0.338 ms | 0.153 ms |
| 64 | 1.632 ms | 1.828 ms | 0.301 ms |
| 128 | 10.705 ms | 11.370 ms | 0.601 ms |
| 256 | 75.978 ms | 80.753 ms | 1.268 ms |

Values are medians of all three completed samples per size, including samples
below the harness signal floor. The [raw export](hexgroebner-cauchy-e74aa3ed6fd5.json),
[source manifest](hexgroebner-cauchy-e74aa3ed6fd5.manifest),
[host/command metadata](hexgroebner-cauchy-e74aa3ed6fd5.measurement.json) and
[complete output](hexgroebner-cauchy-e74aa3ed6fd5.log) retain all 36 samples,
variability, hashes, memory, floor flags and the nonzero harness exit code.
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
count is approximately 13.6 ns without provenance. This is not an isolated
row-update measurement: validation, setup, inversion, decoding and hashing
remain included.

Both dense timing verdicts are **inconclusive**: normalized residual slopes
are `β = -0.324` without provenance and `β = -0.465` with provenance. Three
provenance-enabled samples at `n = 256` fall below the harness signal floor.
Quadratic work predicts growth below the leading cubic law at finite sizes,
but its relative timing contributions have not been separately attributed.
These sweeps do not establish the declared asymptotic timing laws.

The sparse family has `2*n` rows and `256*n` columns, with three nonzeros per
row. Targets duplicate the independent reducers and add zero rank. Direct
sparse reducer installation, bounded active-range scans and one final column
scan give linear source work on this family. Its timing verdict is also
**inconclusive**: all twelve samples are below ten times the measured spawn
floor. The values above are retained observations, not evidence establishing
linear timing. An independent conformance work bound exercises 64 reducers and
64 dependent targets over 100,000 columns, excluding a rows-times-columns
implementation.

The portable accessors still use checked byte operations and `Nat` indices.
Scalar work accounting and metadata allocation remain costs, and intervals
with widely separated nonzeros still inspect their internal gaps. Whole-word
native access, delayed reduction, SIMD, parallelism and attribution of constant
factors remain open. No library phase or performance milestone is claimed.

Retained observations for source fingerprints `71383709ad2f` and `76b276ff26f8`
are in their matching `.json`, `.manifest`, `.measurement.json` and `.log` files.
The former has a cubic-model verdict of inconclusive (`β = -0.262`); the latter
has no verdict-eligible rows at its 100 ms sampling target. Both retain all
twelve completed samples. These are different source/sampling observations,
not a paired before/after performance comparison.

There are no external comparator measurements or correctness-theorem timings.
The fastest-open-source and overall-fastest F4 gaps remain unmeasured under
[#10987](https://github.com/kim-em/hex-dev/issues/10987). Full F4, finite
extensions, complete basis verification and kernel soundness proofs remain
separate deliverables.
