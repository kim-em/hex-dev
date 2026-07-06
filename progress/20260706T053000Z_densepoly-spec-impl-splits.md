# DensePoly executable-layer spec/impl splits (4-PR plan)

Session type: feature (approved plan in ~/.claude/plans, follow-up to
issue #8606 / #8618), stacked branches densepoly-arith-split -> horner-split
-> mulimpl-boxing -> content-split.

## Accomplished

- PR 1 (#8626, merged): add/sub via zipPad toList specs + Array.ofFn impls;
  neg via Array.map impl; derivative via derivList spec + ofFn impl;
  size_derivative_le; six external derivative body-unfolds migrated.
  Key incident: zipPad's first four-clause form compiled via well-founded
  recursion with an AUTO-DERIVED lexicographic measure
  (invImage/Prod.instWellFoundedRelation), which does not kernel-reduce
  (decide +kernel fails) and broke every downstream decide (HexConway
  certificates). Corrected analysis after review: WF recursion is NOT
  kernel-opaque in general -- with an explicit Nat measure the kernel
  reduces it, and plain decide fails only because WF definitions are
  @[irreducible] by default (unseal or decide +kernel unblocks;
  @[semireducible] is warned ineffective for WF). Structural recursion
  remains the right shape for kernel-facing specs: no per-site unseal at
  the ~50 cross-check decides, ordinary defeq, cheaper reduction.
- PR 2 (#8627, CI running): eval/compose noncomputable cons-walk specs
  (evalCoeffList public, new orientation-preserving composeCoeffList) with
  downward Array.foldr impls; composeModMonic same split
  (composeModMonicList); Quotient.eval layer noncomputable on toList.
- PR 3 (mulimpl-boxing, local): acc[k]?.getD -> acc.getD k in mulImpl.
- PR 4 (content-split, local): contentNat/primitivePart toList specs +
  Array.foldl/map impls.

All four validated: full 4142-job builds, HexConformance
(HexGFq.CrossCheck 32 s -> 28 s after PR 1, stable after PR 2), bench
verify checksums (only python-flint runner failures locally), IR checks
(spec symbols absent, impls referenced), Codex reviews (no blocking
findings on any package).

## Current frontier

Waiting on #8627 CI; then push mulimpl-boxing and content-split as PRs in
sequence and merge each when green.

## Next step

Merge train for PRs 2-4; then #8618 can close (PRs 1+2 cover it).
Possible later follow-up from the issue's note: domain-aware trim skip for
field-coefficient products.

## Blockers

None.
