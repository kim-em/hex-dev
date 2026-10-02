/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic

public section

/-!
The bordered-determinant identity `det [[B, u], [vᵀ, x]] = x * det B - vᵀ * adj B * u`,
in the form the producer invariant needs: the block `B` is a selected
submatrix and the border is one more selected row and column. The proof
multiplies on the left by a block lower triangular matrix that clears the
border row, and cancels `det B`.
-/

open Matrix

namespace HexMatrixMathlib

universe u

variable {R : Type u} [CommRing R] [IsDomain R] {n m : Nat}

/-- The bordered-determinant identity for one more selected row and column. -/
theorem det_submatrix_snoc (A : Matrix (Fin n) (Fin m) R) {k : Nat}
    (rows : Fin k → Fin n) (cols : Fin k → Fin m) (p : Fin n) (j : Fin m)
    (hB : (A.submatrix rows cols).det ≠ 0) :
    (A.submatrix (Fin.snoc rows p) (Fin.snoc cols j)).det =
      A p j * (A.submatrix rows cols).det -
        (fun l => A p (cols l)) ⬝ᵥ ((A.submatrix rows cols).adjugate *ᵥ fun l => A (rows l) j) := by
  set B := A.submatrix rows cols with hBdef
  set U : Matrix (Fin k) (Fin 1) R := Matrix.of fun l _ => A (rows l) j
  set V : Matrix (Fin 1) (Fin k) R := Matrix.of fun _ l => A p (cols l)
  set X : Matrix (Fin 1) (Fin 1) R := Matrix.of fun _ _ => A p j
  set e : Fin k ⊕ Fin 1 ≃ Fin (k + 1) := finSumFinEquiv
  have hblocks : (A.submatrix (Fin.snoc rows p) (Fin.snoc cols j)).submatrix e e =
      Matrix.fromBlocks B U V X := by
    ext (i | i) (l | l) <;>
      simp [e, B, U, V, X, Matrix.fromBlocks, Fin.snoc, Fin.natAdd, Fin.last]
  have hdet : (A.submatrix (Fin.snoc rows p) (Fin.snoc cols j)).det =
      (Matrix.fromBlocks B U V X).det := by
    rw [← hblocks, det_submatrix_equiv_self]
  set L : Matrix (Fin k ⊕ Fin 1) (Fin k ⊕ Fin 1) R :=
    Matrix.fromBlocks 1 0 (-(V * B.adjugate)) (Matrix.of fun _ _ => B.det)
  have hL : L.det = B.det := by
    simp [L, det_fromBlocks_zero₁₂]
  have hprod : L * Matrix.fromBlocks B U V X =
      Matrix.fromBlocks B U 0 (-(V * B.adjugate * U) + Matrix.of fun _ _ => B.det * A p j) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.adjugate_mul]
      ext i l
      simp [V, Matrix.mul_apply, mul_comm]
    · ext i l
      simp [X, Matrix.mul_apply, Matrix.add_apply]
  have hcorner : (-(V * B.adjugate * U) + Matrix.of fun _ _ => B.det * A p j).det =
      B.det * A p j - (fun l => A p (cols l)) ⬝ᵥ (B.adjugate *ᵥ fun l => A (rows l) j) := by
    rw [det_fin_one]
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.mul_apply, V, U,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    ring
  have hLM := congrArg Matrix.det hprod
  rw [det_mul, hL, det_fromBlocks_zero₂₁, hcorner, ← hdet] at hLM
  have := mul_left_cancel₀ hB hLM
  rw [this]
  ring

end HexMatrixMathlib
