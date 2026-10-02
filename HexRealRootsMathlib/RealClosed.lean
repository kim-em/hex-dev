/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.FieldTheory.IsRealClosed.Basic

public section

/-! Real-closedness of ℝ from square roots and odd-degree polynomial roots. -/

namespace Real

private theorem real_odd_root (p : Polynomial ℝ) (hp : Odd p.natDegree) :
    ∃ x, p.IsRoot x := by
  by_contra h
  have hleft : ∀ y, p.IsRoot y → y < 0 := fun y hy => False.elim (h ⟨y, hy⟩)
  have hright : ∀ y, p.IsRoot y → 0 < y := fun y hy => False.elim (h ⟨y, hy⟩)
  have hsign : Int.negOnePow (p.natDegree : ℤ) = -1 :=
    Int.negOnePow_odd _ (by exact_mod_cast hp)
  rcases le_total 0 p.leadingCoeff with hlc | hlc
  · have hpos := Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hleft hlc
    have hneg := Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg hright hlc
    rw [hsign] at hneg
    norm_num at hneg
    linarith
  · have hneg := Polynomial.eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos hleft hlc
    have hpos := Polynomial.negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos hright hlc
    rw [hsign] at hpos
    norm_num at hpos
    linarith

/-- The real numbers form a real closed field. -/
instance instIsRealClosed : IsRealClosed ℝ :=
  IsRealClosed.of_linearOrderedField
    (fun {x} hx => ⟨√x, by simpa only [pow_two] using (sq_sqrt hx).symm⟩)
    (fun {p} hp => real_odd_root p hp)

/-- info: 'Real.instIsRealClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instIsRealClosed

end Real
