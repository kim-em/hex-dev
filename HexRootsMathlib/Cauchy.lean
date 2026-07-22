/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Geometry
public import HexRootsMathlib.MahlerPrec
public import Mathlib.Analysis.Polynomial.CauchyBound

public section

/-!
# Coverage by the initial Cauchy square

The executable integer ceiling and base-two ceiling are related to Mathlib's
Cauchy root bound.  Consequently the singleton component used to start the
driver contains every complex root.
-/

open Polynomial Finset

namespace HexRootsMathlib

noncomputable section

private theorem le_foldl_max_init (l : List Int) (init : Nat) :
    init ≤ l.foldl (fun acc a => max acc a.natAbs) init := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldl_cons]
      exact (Nat.le_max_left _ _).trans (ih _)

private theorem le_foldl_max_of_mem (l : List Int) (init : Nat) {a : Int}
    (ha : a ∈ l) :
    a.natAbs ≤ l.foldl (fun acc b => max acc b.natAbs) init := by
  induction l generalizing init with
  | nil => simp at ha
  | cons b l ih =>
      simp only [List.foldl_cons]
      rw [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact (Nat.le_max_right _ _).trans (le_foldl_max_init l _)
      · exact ih _ ha

/-- Every non-leading coefficient is bounded by the exact maximum used in
`cauchyExp`. -/
private theorem coeff_le_cauchyMax (p : Hex.ZPoly) {i : Nat} (hi : i < p.size - 1) :
    (p.coeff i).natAbs ≤
      (p.toArray.extract 0 (p.size - 1)).foldl
        (init := 0) fun acc a => max acc a.natAbs := by
  let a := p.toArray.extract 0 (p.size - 1)
  have hia : i < a.size := by
    simp only [a, Array.size_extract, Hex.DensePoly.toArray_size]
    omega
  have hget : a[i] = p.coeff i := by
    simp only [a, Array.getElem_extract]
    simp only [zero_add]
    rw [Array.getElem_eq_getD (0 : Int)]
    exact Hex.DensePoly.toArray_getD p i
  have hmem : p.coeff i ∈ a.toList := by
    rw [← hget]
    exact Array.getElem_mem_toList hia
  change (p.coeff i).natAbs ≤ a.foldl (fun acc b => max acc b.natAbs) 0
  rw [← Array.foldl_toList]
  exact le_foldl_max_of_mem a.toList 0 hmem

/-- The Mathlib Cauchy bound is no larger than the power of two selected by
the executable integer calculation. -/
theorem cauchyBound_le_two_pow (p : Hex.ZPoly) (h : 0 < p.degree?.getD 0) :
    (Polynomial.cauchyBound (toPolyℂ p) : ℝ) ≤ (2 : ℝ) ^ Hex.cauchyExp p := by
  have hsize : 0 < p.size := by
    by_contra hp
    have hp0 : p.size = 0 := Nat.eq_zero_of_not_pos hp
    simp [Hex.DensePoly.degree?, hp0] at h
  have hdegree : p.degree?.getD 0 = p.size - 1 := by
    rw [Hex.DensePoly.degree?_eq_some_of_pos_size p hsize]
    rfl
  let L := p.leadingCoeff.natAbs
  let M := (p.toArray.extract 0 (p.size - 1)).foldl
    (init := 0) fun acc a => max acc a.natAbs
  let Q := (L + M + L - 1) / L
  have hlead : p.leadingCoeff ≠ 0 := by
    rw [Hex.DensePoly.leadingCoeff_eq_coeff_last p hsize]
    exact Hex.DensePoly.coeff_last_ne_zero_of_pos_size p hsize
  have hL : 0 < L := Int.natAbs_pos.mpr hlead
  have hsup : (Finset.range (toPolyℂ p).natDegree).sup
      (fun i => ‖(toPolyℂ p).coeff i‖₊) ≤ (M : NNReal) := by
    apply Finset.sup_le
    intro i hi
    rw [Finset.mem_range, natDegree_toPolyℂ, hdegree] at hi
    rw [coeff_toPolyℂ, Complex.nnnorm_intCast]
    rw [← NNReal.natCast_natAbs]
    exact_mod_cast coeff_le_cauchyMax p hi
  have hceil : L + M ≤ L * Q := by
    change L + M ≤ L * ((L + M) ⌈/⌉ L)
    exact le_smul_ceilDiv hL
  have hratio : (M : ℝ) / L + 1 ≤ (Q : ℝ) := by
    have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
    rw [div_add_one hLreal.ne']
    apply (div_le_iff₀ hLreal).mpr
    exact_mod_cast (show M + L ≤ Q * L by simpa [Nat.add_comm, Nat.mul_comm] using hceil)
  have hQ : (Q : ℝ) ≤ (2 : ℝ) ^ Hex.ceilLog2 Q := by
    exact_mod_cast le_two_pow_ceilLog2 Q
  calc
    (Polynomial.cauchyBound (toPolyℂ p) : ℝ) =
        (((Finset.range (toPolyℂ p).natDegree).sup
          (fun i => ‖(toPolyℂ p).coeff i‖₊) : NNReal) : ℝ) /
            ‖(toPolyℂ p).leadingCoeff‖₊ + 1 := by
      rfl
    _ ≤ (M : ℝ) / L + 1 := by
      have hleadnorm : (‖(toPolyℂ p).leadingCoeff‖₊ : ℝ) = L := by
        have hleadnormNN : ‖(toPolyℂ p).leadingCoeff‖₊ = (L : NNReal) := by
          rw [Polynomial.leadingCoeff, natDegree_toPolyℂ, hdegree, coeff_toPolyℂ,
            Complex.nnnorm_intCast, ← NNReal.natCast_natAbs,
            ← Hex.DensePoly.leadingCoeff_eq_coeff_last p hsize]
        exact congrArg ((↑) : NNReal → ℝ) hleadnormNN
      rw [hleadnorm]
      gcongr
      exact_mod_cast hsup
    _ ≤ (Q : ℝ) := hratio
    _ ≤ (2 : ℝ) ^ Hex.ceilLog2 Q := hQ
    _ = (2 : ℝ) ^ Hex.cauchyExp p := by
      simp only [Hex.cauchyExp, L, M, Q, if_neg (Nat.ne_of_gt hL)]

/-- Every root of the complex cast lies in the closed square stored in the
executable initial component. -/
theorem isRoot_mem_cauchySquare (p : Hex.ZPoly) (h : 0 < p.degree?.getD 0)
    {z : ℂ} (hz : (toPolyℂ p).IsRoot z) :
    z ∈ DyadicSquare.closedSquare
      ⟨0, 0, -(Hex.cauchyExp p : Int)⟩ := by
  have hp : toPolyℂ p ≠ 0 := by
    intro hp0
    have hnat : (toPolyℂ p).natDegree = p.degree?.getD 0 := natDegree_toPolyℂ p
    rw [hp0, Polynomial.natDegree_zero] at hnat
    omega
  have hroot : ‖z‖ < (Polynomial.cauchyBound (toPolyℂ p) : ℝ) := by
    exact_mod_cast hz.norm_lt_cauchyBound hp
  have hnorm : ‖z‖ < (2 : ℝ) ^ Hex.cauchyExp p :=
    hroot.trans_le (cauchyBound_le_two_pow p h)
  change supNorm
      (z - DyadicSquare.center ⟨0, 0, -(Hex.cauchyExp p : Int)⟩) ≤
    DyadicSquare.halfWidth ⟨0, 0, -(Hex.cauchyExp p : Int)⟩
  have hcenter : DyadicSquare.center
      ⟨0, 0, -(Hex.cauchyExp p : Int)⟩ = 0 := by
    apply Complex.ext <;>
      simp [DyadicSquare.center, Hex.DyadicSquare.center, GaussDyadic.toComplex]
  rw [hcenter, sub_zero]
  calc
    supNorm z ≤ ‖z‖ := max_le (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)
    _ ≤ (2 : ℝ) ^ Hex.cauchyExp p := hnorm.le
    _ = DyadicSquare.halfWidth ⟨0, 0, -(Hex.cauchyExp p : Int)⟩ := by
      rw [DyadicSquare.halfWidth_eq]
      simp

/-- Component-level form of Cauchy coverage: every root occurs in the union
of the squares returned by `Component.cauchy`. -/
theorem exists_mem_component_cauchy (p : Hex.ZPoly) (h : 0 < p.degree?.getD 0)
    {z : ℂ} (hz : (toPolyℂ p).IsRoot z) :
    ∃ s ∈ (Hex.Component.cauchy p h).squares.toList,
      z ∈ DyadicSquare.closedSquare s := by
  refine ⟨⟨0, 0, -(Hex.cauchyExp p : Int)⟩, ?_, isRoot_mem_cauchySquare p h hz⟩
  simp [Hex.Component.cauchy]

end

end HexRootsMathlib
