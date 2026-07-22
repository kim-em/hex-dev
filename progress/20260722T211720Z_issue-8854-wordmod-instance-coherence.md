# issue #8854: canonical WordMod ring operations

## Accomplished

- Moved the `WordMod` natural power, numeral, natural scalar, integer cast, and integer scalar
  instances into `HexModArith/WordMod.lean`, with `toNat_pow`, `toNat_nsmul`, and
  `toNat_neg_mul` as Mathlib-free semantic support.
- Removed the duplicate operation instances from `HexHensel/WordStep.lean` and
  `HexModArithMathlib/WordMod.lean`; both the Grind and Mathlib commutative-ring instances now
  reuse the base operations.
- Reproved the Grind `neg_zsmul` law for cast-then-multiply integer scalar multiplication and
  changed the Mathlib power transport to target the base `WordMod.pow` through `toNat_pow`.
- Lake-built a temporary mixed-import regression module containing the requested `pow_succ` and
  `Lean.Grind.Ring.neg_zsmul` examples; both typechecked.
- Built `HexModArith`, `HexHensel`, `HexModArithMathlib`,
  `HexBerlekampZassenhausMathlib`, and `HexConformance` successfully (9,139 jobs).
- Confirmed `Hex.ZPoly.quadraticHenselStep_eq_bignum` depends exactly on `propext`,
  `Classical.choice`, and `Quot.sound`, and added no `sorry`, `axiom`, or `native_decide`.

## Current frontier

The WordMod operation diamond is eliminated: repository-wide search finds the five affected
operation instances only in the Mathlib-free base, and all requested validation is green.

## Next step

Review and commit the three source changes together with this progress note and the preceding
soundness-review note.

## Blockers

None.
