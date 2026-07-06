# DensePoly executable-layer spec/impl splits (4-PR plan)

Session type: feature (approved plan in ~/.claude/plans, follow-up to
issue #8606 / #8618), stacked branches densepoly-arith-split -> horner-split
-> mulimpl-boxing -> content-split.

## Accomplished

- PR 1 (#8626, merged): add/sub via zipPad toList specs + Array.ofFn impls;
  neg via Array.map impl; derivative via derivList spec + ofFn impl;
  size_derivative_le; six external derivative body-unfolds migrated.
  Key incident: zipPad's first four-clause form compiled via well-founded
  recursion (kernel-opaque, broke every downstream decide, e.g. HexConway
  certificates); restructured to structural recursion on the first list.
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
