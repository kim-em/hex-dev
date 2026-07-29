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
- Passed the 9,629-job full build, Phase 4 report checks, DAG check, focused
  native cross-checks, conformance/release-test targets, the BZ trace gate, and
  the relevant bench smoke gates (including FLINT fixtures in a transient
  `python-flint` environment).
- Refreshed the BZ conformance fixture and trace baseline after the first PR CI
  run exposed the expected canonical factor reordering and newly successful
  non-monic case; the regenerated 102-case fixture passes the FLINT oracle with
  zero failures and the 52-case trace gate passes.

## Current frontier

PR #9068 is open. Its first CI run passed every compilation and benchmark
gate, and identified only the now-refreshed BZ conformance fixture.

## Next step

Push the fixture refresh, monitor the replacement GitHub Actions run to
completion, and merge when green.

## Blockers

None.
