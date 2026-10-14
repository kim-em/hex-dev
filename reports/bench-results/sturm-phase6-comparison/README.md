# Sturm Phase-6 comparison: incomplete high-bit ladder

The required native comparison uses the most recent committed benchmark baseline
`75fbfa04550ae0f76df074176f44bf0f2533334a` and candidate
`8e5b3e40a69117c84bb6f0c19aaad93a26049ab8`. Both frozen binaries, their source
manifests, the built comparison guard and the collector are bound by the
[decision](decision.json.gz) and [manifest](manifest.json).
The successful preflight checks registrations, native fixed hashes and parent
fast checks; it supplies no performance pass.

Collection stopped during the first block at `Hex.SturmBench.runRationalHigh`.
Both sources completed parameters 131072, 262144 and 524288, but the parent
killed parameter 1048576 at its declared 120-second per-call cap. The retained
single-trial, cap-truncated parent reports label the completed rungs consistent
with their declared complexity. Those raw verdicts are not new complexity
evidence. That partial complexity verdict does not complete the four-block
baseline comparison. The collector correctly records `failed`, not a pass or
a completed inconclusive comparison.

Eleven earlier families have a complete adjacent source pair in block zero.
Their data and the partial high-bit pair remain retained; none establishes a
four-block comparison verdict. The peak RSS at parameter 524288 was 12793428 kB
for the baseline and 12801212 kB for the candidate. The per-call observations
were approximately 24.55 and 23.89 seconds. These are source-specific shared-host
observations, not a controlled claim of speedup or regression. Host activity
and CPU affinity are recorded context, with no sample rejection or quiet-core
condition.

The failure consumed the reserved attempt. It is ineligible for an unchanged
rerun under the frozen decision. A changed operational-cap protocol over the same frozen executables first
requires a reviewed collector change: the existing reservation key contains
only the two benchmark binaries and the guard, so a new question or output
directory cannot authorize another attempt. LeanBench supports a matched
`--max-seconds-per-call` override; the current collector provides no such
protocol adaptation. Any changed protocol or meaningful source correction
needs its own decision and bindings, preserving this failed capture, every
declared parameter, balanced blocks and the pinned comparison rule. No cap adaptation or new measurement is included here.
Sturm remains at Phase 5 pending complete computational regression and final
API/use/manual acceptance.

Every archived record uses deterministic gzip. The manifest binds decompressed
bytes and lengths, preserving source manifests, commands, all parent exports,
stdout/stderr, preflight controls, host context, the decision and collector
sources. The [reservation journal](reservation.json.gz) records the consumed attempt
and its finalized context hash. [Binary retention](binary-retention.json)
identifies verified durable copies of both benchmark executables and the guard.
The source manifests identify each frozen source arm; the git fields in raw
baseline exports describe the candidate launch checkout, not baseline origin. Decompress each record before using the existing collector or guard;
a different output directory does not reset its persistent attempt reservation.
