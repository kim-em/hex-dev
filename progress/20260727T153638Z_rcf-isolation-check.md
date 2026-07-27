# Mathlib-free RCF isolation checks

## Accomplished

- Added `HexRCF.IsolationCheck`, containing raw isolation certificate data,
  count/order/completeness validation, and the pure adjacent/all-pairs ordering
  and checker-projection theorems.
- Reduced `HexRCF.Isolations` to literal-isolation packaging and real-root
  semantics while preserving all qualified declaration names through a public
  import.
- Audited direct consumers: `Separation` and `IsolationsTests` both genuinely
  use retained semantic declarations, so their imports remain unchanged.
- Updated the HexRCF umbrella and SPEC file map.
- Verified focused consumers and the full HexRCF build and mechanically checked
  the 30-module `HexRCF.IsolationCheck` closure contains neither `Mathlib.*`
  nor `HexRealRootsMathlib.*`. DAG, Phase-4, release-manifest, trust-surface,
  copyright, diff, and banned-token checks pass. An independent Sol review
  returned GO.

## Current frontier

Issue #8995 is implemented on a branch stacked above the common-root-check PR
#8994. The raw isolation checker is now available to the compiled-core path
without importing literal real-root semantics.

## Next step

Publish the stacked PR, then split strict-gap checks, endpoint classification,
and separation builders from their real-root proofs in `HexRCF.Separation`.
That pure seam is required before executable cell and sign-matrix layers can
drop their Mathlib dependency.

## Blockers

None for this extraction. The branch remains stacked until its parent chain
merges; it can then be rebased and retargeted to main.
