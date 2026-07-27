# Resultant proof kernel and testing-stack repair

## Accomplished

- Merged PR #8882, the exact Brown PRS milestone, after verifying the successful
  GitHub Actions run and retargeted PR #8883 to `main`.
- Diagnosed PR #8945's CI failure as a Phase-4 derivation-comment lint, repaired
  the benchmark comment, and restacked/pushed PRs #8945, #8947, and #8948.
- Proved `powNat_eq_pow` over the lightweight noncommutative semiring interface.
- Proved the strict pseudo-remainder size bound directly from the output-fold
  invariant and normalized dense-polynomial representation.
- Corrected two false NumberField companion contracts by requiring checked
  irreducibility for semantic zero detection and degree preservation.
- Completed focused audits of Resultant, NumberField, and NumberFieldTower,
  including proof inventories, test/documentation gaps, and sound next slices.
- Rebuilt `HexResultant`, `HexNumberFieldMathlib`, and all three benchmark
  executables affected by the testing restack.

## Current frontier

`pseudoDivMod_reconstruct_core` is the remaining primitive Resultant proof.
Its proof needs explicit coefficient/index invariants for the powers, active,
quotient, and remainder folds.  Brown-chain validity should be decomposed only
after that primitive reconstruction theorem is available.

PRs #8945, #8947, and #8948 have fresh Actions runs in progress.  PR #8883 is
retargeted to `main` but needs its stacked branch reconciled with the newly
merged PR #8882 before it can merge.

## Next step

Publish the proof-kernel milestone and leave its independent review monitor
running.  Continue meanwhile with the two local Tower semantic projections
(`NumberTower.toComplex_eq` and `NumberTower.dim_pos`), then return to the
pseudo-division coefficient invariants and the fixed-presentation NumberField
evaluation bridge.

## Blockers

The configured Claude second-opinion OAuth session currently cannot be
refreshed, so no replacement external reviewer is active.  The local Python
environment also lacks `python-flint` and `cypari2`; CI remains the available
external-oracle verification path.
