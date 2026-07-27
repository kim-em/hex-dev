# HexNumberFieldTower arithmetic

## Accomplished

- Added recursive mixed-radix coordinate multiplication: each level convolves
  lower-field blocks and reduces high powers by its stored monic relation.
- Added recursive inversion by top-level polynomial extended gcd, supplying
  coefficient inversion from the lower tower and retaining `0⁻¹ = 0`.
- Added `Zero`, `One`, `Add`, `Sub`, `Neg`, `Mul`, `Inv`, `Div`, rational scalar
  multiplication, and the `NumberTower.Poly` abbreviation.
- Added compiled checks for rational arithmetic, `Q(sqrt 2)`, and the two-level
  tower `Q(sqrt 2, sqrt 3)`, including two-level inversion.
- Built the complete repository successfully.

## Current frontier

Arithmetic on valid raw level data is complete. The next layer must expose the
dependent `Extension` result and construct a genuine one-level tower from a
checked `QAdjoin` presentation, including the selected absolute generator.

## Next step

Implement `Extension`, `ofQAdjoin`, lower-tower embeddings, and the checked
level-construction boundary used later by `adjoin?`.

## Blockers

None.
