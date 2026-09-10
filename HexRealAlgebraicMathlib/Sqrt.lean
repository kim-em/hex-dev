/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Roots
public import HexNumberFieldMathlib.Radical
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section

/-! Certified selection of the unique nonnegative square root. -/

namespace Hex.RealAlgebraicNumber

private theorem complex_sqrt (a : RealAlgebraicNumber) (ha : 0 ≤ a) :
    a.toAlgebraic.sqrt.toComplex = ((Real.sqrt a.toReal : ℝ) : ℂ) := by
  rw [AlgebraicNumber.sqrt_toComplex, ← ofReal_toReal a]
  apply Complex.sqrt_of_nonneg
  change 0 ≤ a.toReal ∧ (0 : ℝ) = 0
  exact ⟨by simpa only [le_iff, zero_toReal] using ha, rfl⟩

/-- A selected square root is nonnegative and squares to its argument. -/
theorem sqrtRoot?_sound (a b : RealAlgebraicNumber) (h : a.sqrtRoot? = some b) :
    0 ≤ b ∧ b ^ 2 = a := by
  unfold sqrtRoot? at h
  split at h
  · contradiction
  · rename_i hn
    have ha : 0 ≤ a := le_of_not_gt hn
    have he := (ofAlgebraic?_eq_some _ b).mp h
    have hv : b.toReal = Real.sqrt a.toReal := by
      have hc := congrArg (fun z : AlgebraicNumber => z.toComplex.re) he
      rw [complex_sqrt a ha] at hc
      exact hc.symm
    refine ⟨?_, toReal_injective ?_⟩
    · rw [le_iff, zero_toReal, hv]
      exact Real.sqrt_nonneg _
    · change (natPow b 2).toReal = a.toReal
      rw [natPow_toReal, hv, Real.sq_sqrt]
      simpa only [le_iff, zero_toReal] using ha

/-- The optimized complex selector supplies a real root for every nonnegative input. -/
theorem sqrtRoot?_isSome (a : RealAlgebraicNumber) (ha : 0 ≤ a) :
    a.sqrtRoot?.isSome = true := by
  rw [sqrtRoot?, ite_eq_right (not_lt_of_ge ha), ofAlgebraic?_isSome, AlgebraicNumber.isReal_iff,
    complex_sqrt a ha]
  rfl

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
