# Mathlib-free RCF cell checks

## Accomplished

- Added `HexRCF.CellsCheck`, containing size-indexed cell data and enumeration,
  exact dyadic samples, endpoint-comparison vectors and validation, and
  bounded-domain relevance checks.
- Reduced `HexRCF.Cells` to root models and real-cell semantics while
  preserving the existing public declaration names through imports.
- Moved the pure strict-gap projection theorem into `HexRCF.SeparationCheck`.
- Replaced a hidden Mathlib simplification dependency in `Cell.size_all` with
  explicit core list lemmas.
- Updated the HexRCF umbrella and SPEC file map.
- Verified focused consumers and the full HexRCF build. Mechanically checked
  that the 35-module `HexRCF.CellsCheck` closure contains neither `Mathlib.*`
  nor `HexRealRootsMathlib.*`; DAG, Phase-4, release-manifest, trust-surface,
  copyright, diff, and banned-token checks pass. An independent Sol review
  returned GO.

## Current frontier

Issue #9000 is implemented on a branch stacked above the separation-check PR
#8999. Executable cell enumeration, sampling, endpoint comparison, and
bounded-domain relevance now have an explicit Mathlib-free boundary.

## Next step

Publish the stacked PR, then extract sign values, sign-entry lookup, and the
sign-matrix certificate replay into a Mathlib-free `HexRCF.SignMatrixCheck`
layer while retaining real-sign semantics in `HexRCF.SignMatrix`.

## Blockers

None for this extraction. The branch remains stacked until its parent chain
merges; it can then be rebased and retargeted to main.
