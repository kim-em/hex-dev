/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Bound
public import HexMatrixMathlib.Hadamard
public import HexMatrixMathlib.Vector
public import HexDeterminantMathlib.CoreTransport

public section

/-! Hadamard's inequality for the executable integer bound. -/

namespace HexModularMatrixMathlib

open HexMatrixMathlib
open scoped BigOperators

private theorem sum_eq (f : Fin n → Nat) : Hex.Matrix.DetBound.sum f = ∑ i, f i := by
  unfold Hex.Matrix.DetBound.sum
  rw [Fin.foldl_eq_finRange_foldl, foldl_finRange_eq_sum]

private theorem prod_eq (f : Fin n → Nat) : Hex.Matrix.DetBound.prod f = ∏ i, f i := by
  unfold Hex.Matrix.DetBound.prod
  rw [Fin.foldl_eq_finRange_foldl, ← List.foldl_map, ← List.prod_eq_foldl,
    ← List.prod_toFinset f (List.nodup_finRange n), List.toFinset_finRange]

private theorem column_bound (A : Hex.Matrix Int n n) :
    (Hex.Matrix.det A).natAbs ≤ Hex.Matrix.DetBound.prod (fun j : Fin n =>
      HexArith.Nat.ceilSqrt (Hex.Matrix.DetBound.sum (fun i : Fin n => A[(i, j)].natAbs ^ 2))) := by
  let B := (matrixEquiv A).map (Int.castRingHom ℝ)
  have hd : B.det = ((Hex.Matrix.det A : Int) : ℝ) := by
    have h := (Int.castRingHom ℝ).map_det (matrixEquiv A)
    rw [← HexMatrixMathlib.det_eq] at h
    exact h.symm
  have hs (j : Fin n) : ∑ i, ‖B i j‖ ^ 2 =
      ((Hex.Matrix.DetBound.sum (fun i : Fin n => A[(i, j)].natAbs ^ 2) : Nat) : ℝ) := by
    simp [B, sum_eq, Nat.cast_sum, Nat.cast_natAbs, Real.norm_eq_abs,
      Hex.Matrix.getElem_pair_eq_nested]
  have hc (j : Fin n) : Real.sqrt (∑ i, ‖B i j‖ ^ 2) ≤
      (HexArith.Nat.ceilSqrt (Hex.Matrix.DetBound.sum
        (fun i : Fin n => A[(i, j)].natAbs ^ 2)) : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨Nat.cast_nonneg _, ?_⟩
    rw [hs]
    exact_mod_cast HexArith.Nat.le_ceilSqrt_sq
      (Hex.Matrix.DetBound.sum (fun i : Fin n => A[(i, j)].natAbs ^ 2))
  have h := (Matrix.norm_det_le_prod_norm_column B).trans
    (Finset.prod_le_prod (fun _ _ => Real.sqrt_nonneg _) (fun j _ => hc j))
  rw [hd] at h
  rw [prod_eq]
  exact_mod_cast (by simpa only [Nat.cast_natAbs, Int.cast_abs, Real.norm_eq_abs, Nat.cast_prod] using h :
    ((Hex.Matrix.det A).natAbs : ℝ) ≤ ∏ j : Fin n,
      (HexArith.Nat.ceilSqrt (Hex.Matrix.DetBound.sum
        (fun i : Fin n => A[(i, j)].natAbs ^ 2)) : ℝ))

/-- The executable row/column Hadamard bound bounds every integer determinant. -/
instance : Hex.Matrix.LawfulDetBound where
  natAbs_det_le A := by
    apply Nat.le_min.mpr
    refine ⟨column_bound A, ?_⟩
    simpa only [Hex.Matrix.det_transpose, Hex.Matrix.getElem_pair_eq_nested,
      Hex.Matrix.getElem_transpose] using column_bound A.transpose

end HexModularMatrixMathlib
