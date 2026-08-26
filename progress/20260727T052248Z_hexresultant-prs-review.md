# HexResultant PRS review repair

## Accomplished

- Rebased the exact Brown PRS milestone onto the merged resultant contract.
- Replaced linear recursive powering with a law-free binary exponentiation
  definition and pinned its association order in the SPEC.
- Added `BrownLaw`, an explicit proof-audit predicate recording nonzero scale
  and divisor obligations, exact reconstruction of both Brown divisions, a
  nonzero successor, and natural termination before fuel exhaustion.
- Added named Phase 1 theorem obligations for ordered-state validity and fuel
  sufficiency, alongside the existing chain invariants.
- Clarified that `PRSResult.scale` belongs to the degree-ordered chain and is
  not by itself the caller-order-sensitive resultant.
- Pinned inference of exact-division laws for both `Int` and `DensePoly Int`.
- Generalized and shortened the integer-polynomial exact-multiple division
  wrapper to `ZPoly.divMod_eq_mul`, removing its unnecessary positive-degree
  hypothesis and updating the factorization consumer.
- Rebuilt `HexResultant` and the affected Berlekamp-Zassenhaus target.

## Current frontier

The PRS executable and its proof surface address the substantive independent
review findings. The worker intentionally continues to call `scaleImpl` and
`divScalarImpl`: the merged SPEC requires those proved runtime twins because
their public list-facing specifications are noncomputable.

## Next step

Run the full repository build, commit and force-push the rebased repair, retarget
PR #8882 to `main`, and launch its asynchronous verification review while
rebasing the resultant-value descendants.

## Blockers

None.
