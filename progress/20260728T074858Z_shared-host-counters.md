# Shared-host counter hardening

## Accomplished

- Treated `chungus2` as the designated release host and replaced global
  quiescence assumptions with pinned-core, SMT-sibling, null-control, and
  fail-closed provenance checks.
- Corrected null interpretation to use a zero-centred maximum-absolute
  envelope, conservatively scaled when the selected control is cheaper.
- Restricted HexRCF acceptance budgets to the three whole-tactic pairs and
  added a check that each budget exceeds the admitted two-arm interference
  ceiling.
- Added an intermediate degree-10 tactic null control after independent review
  identified a possible magnitude gap between the baseline and degree-50
  controls; all controls are now required to precede substantive pairs.
- Replaced idle frequency snapshots with per-arm time-weighted means from
  `cpufreq/stats/time_in_state`; missing residency data fails release quality.
- Preserved signed pinned-CPU residuals, included precise reaped-child and
  harness CPU time, rejected impossible accounting, and set timed Lean work to
  one worker thread.
- Tightened the nominal core-interference ratio to 0.2%, with a recorded
  three-tick quantization floor. A live pinned build on CPU 22 / sibling 70
  produced complete frequency data and no violations.
- Expanded the focused suite to 61 passing tests. Phase-4, DAG, trust-surface,
  line-count, copyright, bench-boundary, Python compile, and diff checks pass.

## Current frontier

The protocol changes are ready for a final independent review. RealRoots
structural PR #8980 is still green-in-progress in its final CI run; this branch
must be rebased onto its merge before collecting release evidence.

## Next step

Obtain a fresh review of the exact protocol commit, fix any verified findings,
then rebase onto merged `main` and run the clean six-round RealRoots sweep on
`chungus2`, pinned to CPU 22.

## Blockers

No host blocker remains. Release evidence cannot be attached to the structural
milestone until PR #8980 merges, but review and protocol validation continue in
parallel.
