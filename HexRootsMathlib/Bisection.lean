/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.RootFree

public section

/-!
# Four-way square subdivision

The executable subdivision produces four closed children.  They cover their
parent exactly; children may overlap on shared boundary segments, which is the
closed-set behavior needed by root-preservation proofs.
-/

namespace HexRootsMathlib

noncomputable section

namespace DyadicSquare

/-- The four closed children returned by executable subdivision cover their
parent square. -/
theorem exists_mem_subdivide {s : Hex.DyadicSquare} {z : ℂ}
    (hz : z ∈ closedSquare s) :
    ∃ t ∈ (Hex.DyadicSquare.subdivide s).toList, z ∈ closedSquare t := by
  let h : _root_.Dyadic := .ofIntWithPrec 1 (s.prec + 1)
  let hr : ℝ := Dyadic.toReal h
  have hhr : 0 < hr := by
    simp only [hr, h, Dyadic.toReal_ofIntWithPrec, Int.cast_one, one_mul]
    exact zpow_pos (by norm_num) _
  have hparent : halfWidth s = 2 * hr := by
    rw [halfWidth_eq]
    simp only [hr, h, Dyadic.toReal_ofIntWithPrec, Int.cast_one, one_mul]
    rw [show -s.prec = -(s.prec + 1) + 1 by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring
  change supNorm (z - center s) ≤ halfWidth s at hz
  have hx : |(z - center s).re| ≤ 2 * hr := by
    rw [← hparent]
    exact (le_max_left _ _).trans hz
  have hy : |(z - center s).im| ≤ 2 * hr := by
    rw [← hparent]
    exact (le_max_right _ _).trans hz
  have hchild : (2 : ℝ) ^ (-(s.prec + 1)) = hr := by
    simp [hr, h, Dyadic.toReal_ofIntWithPrec]
  have hwest (x : ℝ) (hx : |x| ≤ 2 * hr) (hx0 : x ≤ 0) :
      |x + hr| ≤ hr := by
    have habs := (abs_le.mp hx)
    rw [abs_le]
    constructor <;> linarith
  have heast (x : ℝ) (hx : |x| ≤ 2 * hr) (hx0 : ¬x ≤ 0) :
      |x - hr| ≤ hr := by
    have habs := (abs_le.mp hx)
    rw [abs_le]
    constructor <;> linarith
  by_cases hx0 : (z - center s).re ≤ 0 <;>
    by_cases hy0 : (z - center s).im ≤ 0
  · refine ⟨⟨s.re - h, s.im - h, s.prec + 1⟩, ?_, ?_⟩
    · simp [Hex.DyadicSquare.subdivide, h]
    · change supNorm (z - center ⟨s.re - h, s.im - h, s.prec + 1⟩) ≤
        halfWidth ⟨s.re - h, s.im - h, s.prec + 1⟩
      rw [halfWidth_eq, hchild]
      apply max_le
      · have hxb := hwest (z - center s).re hx hx0
        simpa [center, Hex.DyadicSquare.center, GaussDyadic.toComplex,
          Dyadic.toReal_sub, hr, h, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hxb
      · have hyb := hwest (z - center s).im hy hy0
        simpa [center, Hex.DyadicSquare.center, GaussDyadic.toComplex,
          Dyadic.toReal_sub, hr, h, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hyb
  · refine ⟨⟨s.re - h, s.im + h, s.prec + 1⟩, ?_, ?_⟩
    · simp [Hex.DyadicSquare.subdivide, h]
    · change supNorm (z - center ⟨s.re - h, s.im + h, s.prec + 1⟩) ≤
        halfWidth ⟨s.re - h, s.im + h, s.prec + 1⟩
      rw [halfWidth_eq, hchild]
      apply max_le
      · have hxb := hwest (z - center s).re hx hx0
        simpa [center, Hex.DyadicSquare.center, GaussDyadic.toComplex,
          Dyadic.toReal_sub, hr, h, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hxb
      · have hyb := heast (z - center s).im hy hy0
        simpa [center, Hex.DyadicSquare.center, GaussDyadic.toComplex,
          Dyadic.toReal_add, hr, h, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hyb
  · refine ⟨⟨s.re + h, s.im - h, s.prec + 1⟩, ?_, ?_⟩
    · simp [Hex.DyadicSquare.subdivide, h]
    · change supNorm (z - center ⟨s.re + h, s.im - h, s.prec + 1⟩) ≤
        halfWidth ⟨s.re + h, s.im - h, s.prec + 1⟩
      rw [halfWidth_eq, hchild]
      apply max_le
      · have hxb := heast (z - center s).re hx hx0
        simpa [center, Hex.DyadicSquare.center, GaussDyadic.toComplex,
          Dyadic.toReal_add, hr, h, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hxb
      · have hyb := hwest (z - center s).im hy hy0
        simpa [center, Hex.DyadicSquare.center, GaussDyadic.toComplex,
          Dyadic.toReal_sub, hr, h, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hyb
  · refine ⟨⟨s.re + h, s.im + h, s.prec + 1⟩, ?_, ?_⟩
    · simp [Hex.DyadicSquare.subdivide, h]
    · change supNorm (z - center ⟨s.re + h, s.im + h, s.prec + 1⟩) ≤
        halfWidth ⟨s.re + h, s.im + h, s.prec + 1⟩
      rw [halfWidth_eq, hchild]
      apply max_le
      · have hxb := heast (z - center s).re hx hx0
        simpa [center, Hex.DyadicSquare.center, GaussDyadic.toComplex,
          Dyadic.toReal_add, hr, h, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hxb
      · have hyb := heast (z - center s).im hy hy0
        simpa [center, Hex.DyadicSquare.center, GaussDyadic.toComplex,
          Dyadic.toReal_add, hr, h, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hyb

end DyadicSquare

/-- Subdividing every square in an array preserves coverage of their union. -/
theorem exists_mem_subdivideAll {squares : Array Hex.DyadicSquare} {z : ℂ}
    {s : Hex.DyadicSquare} (hs : s ∈ squares.toList)
    (hz : z ∈ DyadicSquare.closedSquare s) :
    ∃ t ∈ (squares.flatMap Hex.DyadicSquare.subdivide).toList,
      z ∈ DyadicSquare.closedSquare t := by
  obtain ⟨t, ht, hzt⟩ := DyadicSquare.exists_mem_subdivide hz
  refine ⟨t, ?_, hzt⟩
  simp only [Array.toList_flatMap, List.mem_flatMap]
  exact ⟨s, hs, ht⟩

/-- A child containing a root survives the elementary `T₀` filter. -/
theorem isRoot_mem_survivors {p : Hex.ZPoly} {squares : Array Hex.DyadicSquare}
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z) {s : Hex.DyadicSquare}
    (hs : s ∈ squares.toList) (hz : z ∈ DyadicSquare.closedSquare s) :
    ∃ t ∈ ((squares.flatMap Hex.DyadicSquare.subdivide).filter
        (fun u => !Hex.rootFree p u)).toList,
      z ∈ DyadicSquare.closedSquare t := by
  obtain ⟨t, ht, hzt⟩ := exists_mem_subdivideAll hs hz
  have hnot : Hex.rootFree p t ≠ true := by
    intro hfree
    exact rootFree_closedSquare hfree hzt hzroot
  have hfalse : Hex.rootFree p t = false := Bool.eq_false_of_not_eq_true hnot
  refine ⟨t, ?_, hzt⟩
  simpa [hfalse] using ht

end

end HexRootsMathlib
