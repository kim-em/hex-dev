/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Sqrt
public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.FieldTheory.IsRealClosed.Basic

public section

/-! Real-closedness obtained from the executable square and polynomial root operations. -/

namespace Hex.RealAlgebraicNumber

/-- Every nonnegative canonical real algebraic number is a square. -/
theorem isSquare_of_nonneg {a : RealAlgebraicNumber} (ha : 0 ≤ a) : IsSquare a := by
  refine ⟨a.sqrt ha, ?_⟩
  simpa only [pow_two] using (sqrt_sq a ha).symm

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

/-- Every odd-degree polynomial has a canonical real root, supplied by the root driver. -/
theorem exists_isRoot_of_odd_natDegree {p : Polynomial RealAlgebraicNumber}
    (hp : Odd p.natDegree) : ∃ a, p.IsRoot a := by
  let f := RealAlgebraicPoly.ofPolynomial p
  have hf : f.toPolynomial = p.map toRealHom := RealAlgebraicPoly.toPolynomial_ofPolynomial p
  have hd : f.toPolynomial.natDegree = p.natDegree := by
    rw [hf, Polynomial.natDegree_map]
  obtain ⟨x, hx⟩ := real_odd_root f.toPolynomial (hd.symm ▸ hp)
  have hm := (RealAlgebraicPoly.contains_roots_iff f x).mpr hx
  cases hroots : f.roots with
  | all =>
    have hz := (RealAlgebraicPoly.roots_all_iff f).mp hroots
    have hn : p.natDegree = 0 := by rw [← hd, hz, Polynomial.natDegree_zero]
    simp [hn] at hp
  | finite entries =>
    rw [hroots] at hm
    obtain ⟨r, _, hr⟩ := hm
    refine ⟨r.root, toReal_injective ?_⟩
    change toRealHom (p.eval r.root) = toRealHom 0
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← hf]
    change f.toPolynomial.eval r.root.toReal = 0
    rwa [hr]

/-- The ordered executable field of canonical real algebraic numbers is real closed. -/
instance instIsRealClosed : IsRealClosed RealAlgebraicNumber :=
  IsRealClosed.of_linearOrderedField isSquare_of_nonneg exists_isRoot_of_odd_natDegree

/-- info: 'Hex.RealAlgebraicNumber.instIsRealClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instIsRealClosed

end Hex.RealAlgebraicNumber
