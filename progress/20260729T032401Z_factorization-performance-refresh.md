# Polynomial factorization performance refresh

## Accomplished

- Accelerated the verified factorization hot path with packed Montgomery
  polynomial kernels, fused normalization, bounded relift probing, and an
  adaptive prime look-ahead while retaining transparent Lean contracts.
- Corrected native extern ownership with borrowed object arguments and added
  runtime-layout warnings for the proof-erased FFI structures. Repeated
  quadratic Hensel runs now remain at 65–69 MiB RSS.
- Replaced a contaminated finite-field timing sample after an A/B/A control,
  refreshed all current Hex factorization artifacts, and retained the already
  current FLINT, PARI/GP, NTL, and Isabelle measurements without rerunning
  them.
- Regenerated all 25 factorization plots and reconciled the aggregate,
  component, profile, and cross-system reports to the final artifacts.
- Recorded a 2.70× public solved-row median speedup over the preceding Hex
  record, 373/392 solved rows, and a 1.09× eligible-row median against verified
  Isabelle BZ, together with the Wilkinson, cutoff-margin, external-system,
  and tactic-import regressions.
- Passed the Phase 4 report checks, DAG check, diff whitespace check, focused
  native cross-checks, and the Mathlib factorization build.

## Current frontier

The implementation, ownership correction, benchmark artifacts, and reports
are ready for final full-tree validation and publication.

## Next step

Rebase onto current `origin/main`, run `lake build`, open the PR, monitor all
GitHub Actions jobs to completion, and merge when green.

## Blockers

None.
