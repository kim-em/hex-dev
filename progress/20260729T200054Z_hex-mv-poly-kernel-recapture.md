# HexMvPoly kernel recapture

## Accomplished

- Captured the v3 kernel proof-probe sweep from clean commit `12cc2559` on
  `chungus2`, pinned to logical CPU 22 with six rotated paired samples.
- Rejected two preliminary captures whose expensive same-module null exceeded
  the preregistered 10% IQR/build cap; retained them outside the worktree for
  audit and did not weaken the validity rule.
- Obtained a release-quality artifact with no validity exceptions, preflight
  failures, or exhausted pairs. Two contaminated pair attempts were retried.
- Measured addition both before and after round-matched construction
  subtraction. Its 4.528× net point ratio is noise-limited because the sorted
  net arithmetic arm lies inside the combined null envelope, so the family
  does not count.
- Recorded resolved largest-rung ratios of 2.001× for cancellation identities
  and 2.579× for SOS certificates. Those two families meet the written gate,
  though cancellation clears it by only 0.1%.
- Replaced the superseded v2 artifact and updated the Mathlib and core
  performance reports, the SPEC's construction-control rule, and the
  future-work representation decision.

## Current frontier

All implementation and measurement evidence for the HexMvPoly SPEC is
complete. The final documentation changes and artifact need verification and
an independent review before the completion PR.

## Next step

Run final report/registry/build checks, commit the recaptured evidence, request
a fresh Claude second opinion, address any findings, then open and land the
completion PR.

## Blockers

None.
