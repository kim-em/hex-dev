/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Roots
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section

/-! Certified selection of the unique nonnegative square root. -/

namespace Hex.RealAlgebraicNumber

private theorem sqrtPolynomial (a : RealAlgebraicNumber) :
    (RealAlgebraicPoly.ofArray #[-a, 0, 1]).toPolynomial =
      Polynomial.X ^ 2 - Polynomial.C a.toReal := by
  rw [RealAlgebraicPoly.toPolynomial_ofArray]
  simp only [← Array.foldr_toList, List.foldr_cons, List.foldr_nil, neg_toReal, zero_toReal,
    one_toReal, Polynomial.C_0, Polynomial.C_1, Polynomial.C_neg]
  ring

private theorem sqrtRoots_finite (a : RealAlgebraicNumber) :
    (RealAlgebraicPoly.ofArray #[-a, 0, 1]).roots ≠ .all := by
  intro hr
  have h := (RealAlgebraicPoly.roots_all_iff _).mp hr
  rw [sqrtPolynomial] at h
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff 2) h
  simp at hc

private theorem sqrtRoots_contains (a : RealAlgebraicNumber) (x : ℝ) :
    (RealAlgebraicPoly.ofArray #[-a, 0, 1]).roots.Contains x ↔ x ^ 2 = a.toReal := by
  rw [RealAlgebraicPoly.contains_roots_iff, sqrtPolynomial]
  simp [sub_eq_zero]

private theorem sqrtRoots_mem (a : RealAlgebraicNumber) (r : RealRootCount)
    (hr : r ∈ (RealAlgebraicPoly.ofArray #[-a, 0, 1]).roots.toArray) :
    r.root.toReal ^ 2 = a.toReal := by
  apply (sqrtRoots_contains a _).mp
  cases h : (RealAlgebraicPoly.ofArray #[-a, 0, 1]).roots with
  | all => exact False.elim (sqrtRoots_finite a h)
  | finite entries =>
    rw [h] at hr
    exact ⟨r, by simpa [RealRootSet.toArray, RealRootSet.finite?] using hr, rfl⟩

/-- A selected square root is nonnegative and squares to its argument. -/
theorem sqrtRoot?_sound (a b : RealAlgebraicNumber) (h : a.sqrtRoot? = some b) :
    0 ≤ b ∧ b ^ 2 = a := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  have hn := Array.find?_some hr
  refine ⟨by simpa only [decide_eq_true_eq] using hn, toReal_injective ?_⟩
  change (natPow r.root 2).toReal = a.toReal
  rw [natPow_toReal]
  exact sqrtRoots_mem a r (Array.mem_of_find?_eq_some hr)

/-- For a nonnegative argument, root completeness supplies a selectable real square root. -/
theorem sqrtRoot?_isSome (a : RealAlgebraicNumber) (ha : 0 ≤ a) :
    a.sqrtRoot?.isSome = true := by
  have har : 0 ≤ a.toReal := by simpa only [le_iff, zero_toReal] using ha
  have hx := (sqrtRoots_contains a (Real.sqrt a.toReal)).mpr (Real.sq_sqrt har)
  have hex : ∃ r ∈ (RealAlgebraicPoly.ofArray #[-a, 0, 1]).roots.toArray, 0 ≤ r.root := by
    cases h : (RealAlgebraicPoly.ofArray #[-a, 0, 1]).roots with
    | all => exact False.elim (sqrtRoots_finite a h)
    | finite entries =>
      rw [h] at hx
      obtain ⟨r, hr, hxr⟩ := hx
      refine ⟨r, by simpa [RealRootSet.toArray, RealRootSet.finite?] using hr, ?_⟩
      rw [le_iff, zero_toReal, hxr]
      exact Real.sqrt_nonneg _
  unfold sqrtRoot?
  rw [Option.isSome_map, Option.isSome_iff_ne_none, ne_eq, Array.find?_eq_none]
  intro hn
  obtain ⟨r, hr, hpos⟩ := hex
  exact hn r hr (by simpa only [decide_eq_true_eq] using hpos)

/-- The checked square-root API succeeds exactly for nonnegative arguments. -/
theorem sqrt?_isSome (a : RealAlgebraicNumber) :
    a.sqrt?.isSome = true ↔ 0 ≤ a := by
  unfold sqrt?
  split
  · rename_i h
    simp [not_le.mpr h]
  · rename_i h
    simp [sqrtRoot?_isSome a (le_of_not_gt h), le_of_not_gt h]

/-- A successful checked square root has the specified value. -/
theorem sqrt?_sound (a b : RealAlgebraicNumber) (h : a.sqrt? = some b) :
    0 ≤ b ∧ b ^ 2 = a := by
  unfold sqrt? at h
  split at h
  · contradiction
  · exact sqrtRoot?_sound a b h

/-- The proof-carrying square root never takes its fallback. -/
theorem sqrt?_eq_some (a : RealAlgebraicNumber) (ha : 0 ≤ a) :
    a.sqrt? = some (a.sqrt ha) := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((sqrt?_isSome a).mpr ha)
  simp only [sqrt, hb, Option.getD_some]

/-- The selected square root is nonnegative. -/
theorem sqrt_nonneg (a : RealAlgebraicNumber) (ha : 0 ≤ a) : 0 ≤ a.sqrt ha :=
  (sqrt?_sound a _ (sqrt?_eq_some a ha)).1

/-- Squaring the selected square root recovers the argument. -/
theorem sqrt_sq (a : RealAlgebraicNumber) (ha : 0 ≤ a) : (a.sqrt ha) ^ 2 = a :=
  (sqrt?_sound a _ (sqrt?_eq_some a ha)).2

/-- The executable square root agrees with the nonnegative real square root. -/
theorem sqrt_toReal (a : RealAlgebraicNumber) (ha : 0 ≤ a) :
    (a.sqrt ha).toReal = Real.sqrt a.toReal := by
  have hn : 0 ≤ (a.sqrt ha).toReal := by
    simpa only [le_iff, zero_toReal] using sqrt_nonneg a ha
  have hs := congrArg toReal (sqrt_sq a ha)
  change (natPow (a.sqrt ha) 2).toReal = a.toReal at hs
  rw [natPow_toReal] at hs
  rw [← hs, Real.sqrt_sq hn]

/-- A nonnegative square root is unique. -/
theorem sqrt_unique (a b : RealAlgebraicNumber) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hs : b ^ 2 = a) : a.sqrt ha = b := by
  apply toReal_injective
  rw [sqrt_toReal]
  have hs' := congrArg toReal hs
  change (natPow b 2).toReal = a.toReal at hs'
  rw [natPow_toReal] at hs'
  rw [← hs', Real.sqrt_sq (by simpa only [le_iff, zero_toReal] using hb)]

/-- Taking the nonnegative square root of a square yields the absolute value. -/
theorem sqrt_square (a : RealAlgebraicNumber) :
    (a ^ 2).sqrt (sq_nonneg a) = a.abs := by
  apply sqrt_unique
  · rw [abs_eq]
    exact abs_nonneg a
  · rw [abs_eq, sq_abs]

/-- Negative inputs are rejected, and only negative inputs are rejected. -/
theorem sqrt?_eq_none (a : RealAlgebraicNumber) : a.sqrt? = none ↔ a < 0 := by
  rw [← Option.not_isSome_iff_eq_none, sqrt?_isSome, not_le]

end Hex.RealAlgebraicNumber
