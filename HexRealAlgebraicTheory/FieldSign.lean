/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealAlgebraic.FieldSign
public import HexRealAlgebraicTheory.Order
public import HexNumberFieldTheory.RealSign
public section
namespace Hex.RealAlgebraicNumber

/-- The interval-based field sign agrees with the selected real embedding. -/
theorem signField_spec (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic) :
    signField generator value =
      (SignType.sign (PolyQuot.toComplex value generator.toAlgebraic.rep
        generator.toAlgebraic.rep_mk).re : Int) :=
  QAdjoin.signApprox_spec value generator.property

/-- The fast sign equals the existing canonical sign for a real field coordinate. -/
theorem signField_eq (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic)
    (real : value.toAlgebraicNumber.isReal = true) :
    signField generator value = (ofAlgebraic value.toAlgebraicNumber real).sign := by
  rw [signField_spec, sign_eq]
  change _ = (if value.toAlgebraicNumber.toComplex.re < 0 then (-1 : Int)
    else if value.toAlgebraicNumber.toComplex.re = 0 then 0 else 1)
  have mapped : value.toAlgebraicNumber.toComplex =
      PolyQuot.toComplex value generator.toAlgebraic.rep generator.toAlgebraic.rep_mk :=
    PolyQuot.toAlgebraicNumber_toComplex value generator.toAlgebraic.rep
      generator.toAlgebraic.rep_mk
  rw [mapped]
  rcases lt_trichotomy (PolyQuot.toComplex value generator.toAlgebraic.rep
      generator.toAlgebraic.rep_mk).re 0 with negative | zero | positive
  · rw [sign_eq_neg_one_iff.mpr negative]
    simp [negative]
  · rw [zero]
    simp
  · rw [sign_eq_one_iff.mpr positive]
    simp [not_lt.mpr positive.le, ne_of_gt positive]
end Hex.RealAlgebraicNumber
