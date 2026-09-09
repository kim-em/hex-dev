/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Order
public import HexNumberFieldMathlib.Nearest
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Algebra.Order.Ring.InjSurj
public section

/-! Exact comparisons agree with Mathlib's complex partial order. -/
namespace Hex.AlgebraicNumber

private theorem compare_sub (x y : ℝ) : compare 0 (y - x) = compare x y := by
  rcases lt_trichotomy x y with h | h | h
  · rw [compare_lt_iff_lt.mpr (sub_pos.mpr h), compare_lt_iff_lt.mpr h]
  · subst y
    simp
  · rw [compare_gt_iff_gt.mpr (sub_neg.mpr h), compare_gt_iff_gt.mpr h]

/-- Partial comparison detects exactly equal imaginary parts and compares real parts. -/
theorem partialCompare_eq (a b : AlgebraicNumber) :
    partialCompare a b = if a.toComplex.im = b.toComplex.im then
      some (compare a.toComplex.re b.toComplex.re) else none := by
  unfold partialCompare
  split
  · rename_i hab
    have h := (beq_iff a b).mp hab
    simp [h]
  · split
    · rename_i hreal
      simp only [Bool.and_eq_true] at hreal
      obtain ⟨ha, hb⟩ := hreal
      rw [realCompare_eq a b ha hb]
      simp [(isReal_iff a).mp ha, (isReal_iff b).mp hb]
    · split
      · rename_i hside
        have hi : a.toComplex.im ≠ b.toComplex.im := fun h =>
          hside (OrientedIsolation.side_eq_of_im_eq a.isolation b.isolation h)
        simp [hi]
      · dsimp only
        split
        · rename_i hreal
          have hi : a.toComplex.im = b.toComplex.im := by
            have h := (isReal_iff (b - a)).mp hreal
            rw [sub_toComplex, Complex.sub_im] at h
            exact (sub_eq_zero.mp h).symm
          have hz : (0 : AlgebraicNumber).isReal = true :=
            (isReal_iff _).mpr (by rw [zero_toComplex]; rfl)
          rw [realCompare_eq _ _ hz hreal, zero_toComplex, sub_toComplex]
          simp [hi, compare_sub]
        · rename_i hreal
          have hi : a.toComplex.im ≠ b.toComplex.im := by
            intro hi
            apply hreal
            apply (isReal_iff _).mpr
            simp [sub_toComplex, hi]
          simp [hi]

/-- The executable non-strict comparison has Mathlib's complex semantics. -/
theorem le_iff (a b : AlgebraicNumber) :
    a ≤ b ↔ a.toComplex.re ≤ b.toComplex.re ∧ a.toComplex.im = b.toComplex.im := by
  change (partialCompare a b).any (fun o => o != .gt) = true ↔ _
  rw [partialCompare_eq]
  split <;> simp_all [compare_gt_iff_gt, not_lt]

/-- The executable strict comparison has Mathlib's complex semantics. -/
theorem lt_iff (a b : AlgebraicNumber) :
    a < b ↔ a.toComplex.re < b.toComplex.re ∧ a.toComplex.im = b.toComplex.im := by
  change partialCompare a b = some .lt ↔ _
  rw [partialCompare_eq]
  split <;> simp_all [compare_lt_iff_lt]

instance : PartialOrder AlgebraicNumber where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl a := (le_iff _ _).mpr ⟨le_rfl, rfl⟩
  le_trans a b c hab hbc := (le_iff _ _).mpr
    ⟨((le_iff _ _).mp hab).1.trans ((le_iff _ _).mp hbc).1,
     ((le_iff _ _).mp hab).2.trans ((le_iff _ _).mp hbc).2⟩
  le_antisymm a b hab hba := toComplex_injective (Complex.ext
    (((le_iff _ _).mp hab).1.antisymm ((le_iff _ _).mp hba).1)
    ((le_iff _ _).mp hab).2)
  lt_iff_le_not_ge a b := by
    rw [lt_iff, le_iff, le_iff]
    constructor
    · rintro ⟨hr, hi⟩
      exact ⟨⟨hr.le, hi⟩, fun h => (not_le_of_gt hr) h.1⟩
    · rintro ⟨⟨hr, hi⟩, hn⟩
      exact ⟨lt_of_le_not_ge hr (fun h => hn ⟨h, hi.symm⟩), hi⟩

open scoped ComplexOrder

instance : IsStrictOrderedRing AlgebraicNumber :=
  Function.Injective.isStrictOrderedRing toComplex zero_toComplex one_toComplex
    add_toComplex mul_toComplex (fun {a b} => (le_iff a b).symm)
    (fun {a b} => (lt_iff a b).symm)

/-- Interpretation is an embedding for the complex partial order. -/
noncomputable def toComplexOrder : AlgebraicNumber ↪o ℂ where
  toFun := toComplex
  inj' := toComplex_injective
  map_rel_iff' := fun {a b} => (le_iff a b).symm

end Hex.AlgebraicNumber
