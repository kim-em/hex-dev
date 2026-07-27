# HexNumberField algebraic-polynomial representation

## Accomplished

- Added the constructor-sealed `AlgebraicPoly` representation for arrays of
  canonical algebraic coefficients.
- Made `ofArray` remove semantic trailing zeros through
  `AlgebraicNumber.isZero`, without requiring a kernel `DecidableEq` instance.
- Added normalized coefficient access, size, degree, zero, and Boolean equality
  operations together with compiled zero-normalization checks.
- Exported the new module from the `HexNumberField` umbrella and rebuilt both
  targets successfully.

## Current frontier

The Mathlib-free algebraic-coefficient polynomial boundary is complete. The
next implementation layer is fixed-field root computation: squarefree
decomposition, norm eliminants, isolation, and bounded embedding
disambiguation.

## Next step

Implement the fixed-field polynomial/root primitives and then expose
`QAdjoin.roots?` and its total wrapper.

## Blockers

None.
