# Mathlib-free RCF carrier checks

## Accomplished

- Added `HexRCF.CarrierCheck`, containing the carrier certificate data,
  Boolean validation, proposition-level checker consequences, and the pure
  carrier/product nonzero theorems.
- Reduced `HexRCF.Carrier` to real-polynomial squarefreeness and root-set
  semantics while preserving all qualified declaration names through a public
  import.
- Narrowed `HexRCF.Builder`'s direct carrier dependency to `CarrierCheck`;
  its remaining Mathlib closure comes through the still-combined common-root
  and sign-matrix layers.
- Updated the HexRCF umbrella and SPEC file map.
- Verified targeted and full HexRCF builds and mechanically checked the
  31-module `HexRCF.CarrierCheck` closure contains neither `Mathlib.*` nor
  `HexRealRootsMathlib.*`. DAG, Phase-4, release-manifest, trust-surface,
  copyright, diff, and banned-token checks pass. An independent Sol review
  returned GO.

## Current frontier

Issue #8990 is implemented on a branch stacked above the Sturm-check PR #8988.
The pure syntax, replay checker/builder, and carrier checker now form a
source-compatible Mathlib-free certificate prefix.

## Next step

Publish the stacked PR, then extract common-root certificate validation and
its cached interval query from `HexRCF.CommonRoot` so compiled arithmetic
preparation can depend on another pure checker seam.

## Blockers

None for this extraction. The branch remains stacked until #8988 and its
syntax parent #8983 merge; it can then be rebased and retargeted to main.
