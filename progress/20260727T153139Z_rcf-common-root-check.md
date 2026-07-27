# Mathlib-free RCF common-root checks

## Accomplished

- Added `HexRCF.CommonRootCheck`, containing common-root certificate data,
  replay/divisibility/Bezout validation, proposition-level checker
  consequences, nonzero and replay recovery, and the executable cached
  interval query.
- Reduced `HexRCF.CommonRoot` to real-root, isolation, and root-cell semantics
  while preserving all qualified declaration names through a public import.
- Narrowed `HexRCF.Builder`'s direct common-root dependency to
  `CommonRootCheck`; its remaining Mathlib closure comes through the
  still-combined sign-matrix layer.
- Updated the HexRCF umbrella and SPEC file map.
- Verified targeted consumers and the full HexRCF build and mechanically
  checked the 30-module `HexRCF.CommonRootCheck` closure contains neither
  `Mathlib.*` nor `HexRealRootsMathlib.*`. DAG, Phase-4, release-manifest,
  trust-surface, copyright, diff, and banned-token checks pass. An independent
  Sol review returned GO.

## Current frontier

Issue #8993 is implemented on a branch stacked above the carrier-check PR
#8991. Syntax, replay, carrier, and common-root validation now have explicit
Mathlib-free module boundaries.

## Next step

Publish the stacked PR, then extract the raw isolation certificate checks and
their pure ordering/count consequences from `HexRCF.Isolations` as the next
dependency needed by a pure sign-matrix/certificate replay path.

## Blockers

None for this extraction. The branch remains stacked until the syntax, Sturm,
and carrier parents merge; it can then be rebased and retargeted to main.
