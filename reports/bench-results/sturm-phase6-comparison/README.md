# Original Sturm comparison: incomplete high-bit ladder

The separately reviewed cap-adapted campaign now
[passes all 58 families](cap-complete-v3/README.md). The account below describes
the original failed capture; its raw records and consumed reservation remain
unchanged.

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
single-trial parent reports from a ladder killed at the per-call cap label the completed rungs consistent
with their declared complexity. Those raw verdicts are not new complexity
evidence. That partial complexity verdict does not complete the four-block
baseline comparison. The collector correctly records `failed`, not a pass or
a completed inconclusive comparison.

Only 12 of the 58 declared timing families were attempted in block zero:
11 have complete adjacent source pairs and the twelfth has partial ladders.
The remaining 46 families and blocks one through three never started.
Status `killed_at_cap` is a per-call termination, distinct from the parent
`budget_truncated: false` metadata.
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
`--max-seconds-per-call` override; the collector retained with this capture provides no such
protocol adaptation. Any changed protocol or meaningful source correction
needs its own decision and bindings, preserving this failed capture, every
declared parameter, balanced blocks and the pinned comparison rule. The [cap adaptation contract](cap-protocol.md) describes the separate collector
support and proposed complete campaign. These retained artifacts contain no
revised-campaign measurements.
Any proposed cap protocol must address the complete selected family list,
including the unattempted reduced/replay high-bit families and repeated
prepared-query families, before reserving a new campaign. The existing
reservation is enforced on host `chungus2` at the recorded state path; deleting
or changing the state location does not authorize an unchanged retry. A rebuilt
executable with a different digest needs verified source/build bindings and a
new explicit decision, rather than treating a digest change as permission.
This original partial capture alone cannot satisfy computational regression
or final API/use/manual acceptance.

Every archived record uses deterministic gzip. The manifest binds decompressed
bytes and lengths, preserving source manifests, commands, all parent exports,
stdout/stderr, preflight controls, host context, the decision and collector
sources. The [reservation journal](reservation.json.gz) records the consumed attempt
and its finalized context hash. [Binary retention](binary-retention.json)
identifies verified durable copies of both benchmark executables and the guard.
The source manifests identify each frozen source arm; the git fields in raw
baseline exports and stdout describe the candidate launch checkout, not baseline origin. Decompress each record before using the existing collector or guard;
a different output directory does not reset its persistent attempt reservation.

The retained executable copies are durable host-local files on `chungus2`.
This record does not claim an independent backup or availability on other hosts.
