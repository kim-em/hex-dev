# Mathlib-free RCF separation checks

## Accomplished

- Added `HexRCF.SeparationCheck`, containing strict-gap validation and pure
  dyadic consequences, endpoint comparison data and executable classification,
  replay-based interval refinement/separation builders, and output-retention
  soundness.
- Reduced `HexRCF.Separation` to `RootCmp.Holds` and real-root ordering and
  endpoint-classifier semantics while preserving all public declaration names.
- Replaced the proof-only Mathlib order helper with the core
  `Init.Data.Order.Lemmas` / `Std.lt_trans` operation.
- Made `SeparationTests` import all of the checker module explicitly so kernel
  reduction sees the moved non-exposed builder bodies.
- Updated the HexRCF umbrella and SPEC file map.
- Verified focused consumers and the full HexRCF build and mechanically checked
  the 33-module `HexRCF.SeparationCheck` closure contains neither `Mathlib.*`
  nor `HexRealRootsMathlib.*`. DAG, Phase-4, release-manifest, trust-surface,
  copyright, diff, and banned-token checks pass. An independent Sol review
  returned GO.

## Current frontier

Issue #8997 is implemented on a branch stacked above the isolation-check PR
#8996. Strict isolation and endpoint comparison computation now have an
explicit Mathlib-free boundary.

## Next step

Publish the stacked PR, then separate executable cell data/sampling and bounded
domain comparison checks from the `RootModel` and real-cell semantics in
`HexRCF.Cells`. That module boundary will unblock a pure sign-matrix replay
layer.

## Blockers

None for this extraction. The branch remains stacked until its parent chain
merges; it can then be rebased and retargeted to main.
