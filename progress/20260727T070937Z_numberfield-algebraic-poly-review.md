# HexNumberField AlgebraicPoly review repair

## Accomplished

- Verified the independent review's representation-level counterexample:
  constructor privacy alone did not make trailing-zero normalization available
  to theorems quantified over every `AlgebraicPoly`.
- Added the erased `AlgebraicPolyNormalized` invariant to the private
  representation and proved that semantic `Array.popWhile` establishes it.
- Retained the private constructor boundary; downstream companion proofs can
  use the public `normalized` projection without unfolding the smart
  constructor.
- Rebuilt `HexNumberField.AlgebraicPoly` successfully.

## Current frontier

The central companion obligation `AlgebraicPoly.isZero_iff` is no longer
refutable by a malformed trailing-zero inhabitant.

## Next step

Push the repair, rebase the fixed-field and common-field root milestones over
it, and continue with the tower layer while outstanding reviews run.

## Blockers

None.
