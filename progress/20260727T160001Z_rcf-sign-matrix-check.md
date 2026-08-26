# Mathlib-free RCF sign-matrix replay

## Accomplished

- Added `HexRCF.SignMatrixCheck`, containing exact sign data and dyadic
  evaluation, coefficient-based polynomial deduplication, common-root package
  alignment, open/root-cell sign lookup, sign-row caching, Boolean comparison
  and formula evaluation, and per-cell certificate replay.
- Reduced `HexRCF.SignMatrix` to real-polynomial, semantic-cell, and reflected
  formula correctness theorems while preserving existing public names through
  imports.
- Replaced the hidden Mathlib-only `Bool.eq_false_of_not_eq_true` proof helper
  with a core Boolean case proof and made the core list dependency explicit.
- Rewired `Builder` and `Certificate` to `SignMatrixCheck`; `Soundness` now owns
  the semantic `SignMatrix` import explicitly, and `BuilderTests` requests the
  checker implementation in its meta import.
- Updated the HexRCF umbrella and SPEC file map.
- Verified focused consumers and the full HexRCF build. Mechanically checked
  the 39-module `SignMatrixCheck`, 40-module `Certificate`, and 41-module
  `Builder` closures contain neither `Mathlib.*` nor
  `HexRealRootsMathlib.*`; DAG, Phase-4, release-manifest, trust-surface,
  copyright, diff, and banned-token checks pass. An independent Sol review
  verified all 56 declarations and 21 exposure annotations and returned GO.

## Current frontier

Issue #9003 is implemented on a branch stacked above the cell-check PR #9002.
The complete kernel-facing certificate replay and its compiled witness builder
now have mechanically verified Mathlib-free import closures.

## Next step

Publish the stacked PR, then use the new pure certificate boundary to finish
the generic-vs-tactic Phase-4 evidence and promote the green extraction stack
as each parent reaches `main`.

## Blockers

None for this extraction. The branch remains stacked until its parent chain
merges; it can then be rebased and retargeted to main.
