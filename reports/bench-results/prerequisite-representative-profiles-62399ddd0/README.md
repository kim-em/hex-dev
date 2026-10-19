# Retained prerequisite representative profiles

These three native-kernel captures supply representative attribution for the
implemented Sturm and real-algebraic surfaces. They use clean source
`62399ddd0cc7416287cafcfb19c51bc6184aef6d`; computational source and executable
hashes, commands, tool versions and host context are in each manifest.
The driver snapshot is retained unchanged in `capture.py.txt`.

| Capture | Timed runner and parameter | Samples | Calibration residual ms | Allocation % | Dominant inclusive phase % |
| --- | --- | --- | --- | --- | --- |
| Sturm replay | `runFieldReplay`, 20 | 548 | 0.546 | 46.35 | Certificate replay 99.82; signed-chain check 77.74 |
| Prepared Sturm query | `runPreparedHigh`, 65536 | 526 | 0.650 | 27.19 | Signed-chain build 92.02; pseudo-division 87.45 |
| Canonical real addition | `runHardAdd`, 0 | 6592 | 0.046 | 42.38 | Root isolation 91.88; refinement 90.61 |

All three pass the kernel-window sample-count, calibration and ±5 ms
sensitivity checks. Inclusive phases overlap and must not be added together.
The shared host was used as observed: captures ran serially on automatically
leased CPUs, without an idle-core preflight or a load rejection rule.

Raw perf data, original and normalized samply profiles, kernel-window sidecars,
symbols, diagnostics, source snapshots and command stdout/stderr remain under
`/home/kim/.local/state/hex/issue-10577-profiles/` at the paths in the manifests.
`artifact-check.json` records 126 matching artifact checksums, 42 per capture.
Each manifest records every raw artifact's SHA-256; these files can be
reprocessed while that persistent storage remains available.
`binary-retention.json` also records persistent copies of both exact profiled
executables, verified against the manifests' hashes, for native symbolization.

The earlier 38 raw captures were lost after a reboot. Their completed
measurements, manifests, summaries and failed/inconclusive verdicts remain in
the existing evidence and are not replaced by these captures. These profiles
provide attribution only: they are not scientific timing sweeps, fixed-budget
passes or a justification for admitting an unresolved complexity model.
