# HexNumberField fixed-presentation minimal polynomials

## Accomplished

- Added the multiplication-by-element matrix in the defining polynomial's
  power basis.
- Implemented exact Krylov-orbit row reduction to recover the first monic
  rational relation, then clear denominators and normalize its primitive
  integer part.
- Implemented checked and total `QAdjoin` conversion to canonical
  `AlgebraicNumber`, including executable normalization checks, root isolation,
  guarded ball evaluation, and certified root matching.
- Kept the new API in `Convert.lean`, matching the SPEC file organization.
- Added compiled regressions for `sqrt 2` and `1 + sqrt 2` and rebuilt both
  `HexNumberField.Convert` and the umbrella `HexNumberField` target.

## Current frontier

The complete executable fixed-presentation canonicalization path is present.
The Mathlib companion still needs the semantic Krylov/minimal-polynomial proof,
root-selection uniqueness, and `_isSome` theorem that retire the total
wrapper's checked fallback.

## Next step

Publish this milestone as a stacked PR, launch its independent review monitor,
and begin the lazy arithmetic/eliminant stage without waiting for that review.

## Blockers

None.
