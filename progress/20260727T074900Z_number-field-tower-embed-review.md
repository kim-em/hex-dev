# Number-field tower embedding review fixes

## Accomplished

- Added conjugate-sensitive regressions that inspect the stored isolating
  square, including a negative root of `X² - 2`.
- Made linear rational presentations return the identity extension of `rat`
  rather than constructing a second height-one representation of `Q`.
- Derived the monic quotient relation consistently from the sign-normalized
  polynomial stored by the absolute root.
- Reused `ZPoly.normalizePrimitiveSign` instead of maintaining a duplicate
  sign-normalization implementation.
- Added a non-unit-leading regression for `2X² - 3` and retained the selected
  isolation through construction.
- Verified `lake build HexNumberFieldTower.Basic` and
  `lake build HexNumberFieldTower.Embed`.

## Current frontier

The executable constructor now covers embedding selection, linear identity,
global sign, and rational monic normalization. Levels still need a meaningful
stored relative-irreducibility invariant suitable for the Mathlib field-law
proofs; a detached Boolean marker would not be sufficient.

## Next step

Design the level certificate around the recursive factor checker so it is
definitionally tied to the stored relative polynomial, then thread it through
all smart constructors before beginning the Mathlib tower laws.

## Blockers

None.
