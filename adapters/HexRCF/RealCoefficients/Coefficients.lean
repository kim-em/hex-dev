/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Order
public import HexNumberFieldMathlib.CommonField
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

/-! Checked real interpretations of existing algebraic-number coefficients. -/

namespace Hex.RCF.RealCoefficients.Coefficients

/-- Convert a fixed-field result while retaining its generator's real embedding.
Arithmetic producing `value` remains the existing `QAdjoin` arithmetic. -/
@[expose] def ofField (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic) : RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic value.toAlgebraicNumber (by
    rw [AlgebraicNumber.isReal_iff, QAdjoin.toAlgebraicNumber,
      PolyQuot.toAlgebraicNumber_toComplex]
    exact QAdjoin.value_real value generator.property)

/-- The conversion preserves the selected complex value, not an arbitrary conjugate. -/
theorem ofField_value (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic) :
    ((ofField generator value).toReal : ℂ) =
      PolyQuot.toComplex value generator.toAlgebraic.rep generator.toAlgebraic.rep_mk := by
  rw [RealAlgebraicNumber.ofReal_toReal]
  exact PolyQuot.toAlgebraicNumber_toComplex value _ _

/-- Nonnegativity and the exact power equation authenticate a higher-root alias.
The degree is positive and the base nonnegative; negative-base `rpow` has
different semantics and cannot use this theorem. -/
theorem root_alias (root : RealAlgebraicNumber) (base : ℝ) (degree : Nat)
    (hdegree : degree ≠ 0) (hbase : 0 ≤ base) (hroot : 0 ≤ root.toReal)
    (hpower : root.toReal ^ degree = base) :
    root.toReal = base ^ (1 / (degree : ℝ)) := by
  apply (pow_left_inj₀ hroot (Real.rpow_nonneg hbase _) hdegree).mp
  rw [hpower, one_div, Real.rpow_inv_natCast_pow hbase hdegree]

end Hex.RCF.RealCoefficients.Coefficients
