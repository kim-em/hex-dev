# HexResultant PRS audit fixes

## Accomplished

- Packaged the existing Mathlib-free dense-polynomial laws as recursive
  `Lean.Grind.Semiring`, `Ring`, and `CommRing` instances, so the resultant
  correctness surface now instantiates for polynomial coefficient rings.
- Added coherent dense-polynomial casts, scalar actions, powers, coefficient
  lemmas, and an explicit `powNat_eq_pow` proof obligation.
- Strengthened `BrownLaw` with nonzero adjacent terms, strict size descent,
  nonzero successor scale, and list-facing exact-division equations.
- Added the missing `subresultantChain_zero_left` equation and value-level
  exact-division, binary-power, and nested defective-chain regressions.
- Rebuilt `HexResultant` successfully.

## Current frontier

The substantive PRS review findings are addressed. Lower-priority cleanup
suggestions about public helper visibility, an avoidable final squaring in
`powNat`, and a separately over-restricted `ZPoly.divMod_eq_mul` lemma remain
non-blocking refinements.

## Next step

Push the PRS audit repair, propagate it through the stacked resultant and
number-field branches, then resume the fixed-field minimal-polynomial stage.

## Blockers

None.
