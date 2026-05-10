import HexMatrixMathlib.Basic
import HexMatrix.RREF
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
Rank, row-span, and nullspace bridge theorems for `hex-matrix-mathlib`.

This module converts the executable `Hex.Matrix` row-reduction data into
Mathlib's function-based matrix model, then states bridge theorems relating
computed rank, span membership, and nullspace bases to Mathlib's
noncomputable linear-algebra definitions.
-/

namespace HexMatrixMathlib

universe u

variable {R : Type u} {n m : Nat}

/-- Convert an executable `Vector` into Mathlib's function representation. -/
def vectorEquiv : Vector R n ≃ (Fin n → R) where
  toFun := fun v i => v[i]
  invFun := Vector.ofFn
  left_inv := by
    intro v
    ext i
    simp
  right_inv := by
    intro f
    funext i
    simp

@[simp] theorem vectorEquiv_apply (v : Vector R n) (i : Fin n) :
    vectorEquiv v i = v[i] :=
  rfl

@[simp] theorem vectorEquiv_symm_apply (f : Fin n → R) (i : Fin n) :
    (vectorEquiv.symm f)[i] = f i := by
  simp [vectorEquiv]

@[simp] theorem matrixEquiv_row (M : Hex.Matrix R n m) (i : Fin n) :
    _root_.Matrix.row (matrixEquiv M) i = vectorEquiv (Hex.Matrix.row M i) := by
  funext j
  simp [Hex.Matrix.row]

private theorem foldl_finRange_eq_sum [AddCommMonoid R] {n : Nat} (f : Fin n → R) :
    (List.finRange n).foldl (fun acc i => acc + f i) 0 = ∑ i, f i := by
  rw [← List.foldl_map]
  rw [← List.sum_eq_foldl]
  rw [← List.sum_toFinset f (List.nodup_finRange n)]
  rw [List.toFinset_finRange]

private theorem vectorEquiv_mulVec [Field R] (M : Hex.Matrix R n m) (v : Vector R m) :
    vectorEquiv (M * v) = (matrixEquiv M).mulVec (vectorEquiv v) := by
  funext i
  simp only [vectorEquiv_apply]
  change (Hex.Matrix.mulVec M v)[i.val] = (matrixEquiv M).mulVec (vectorEquiv v) i
  unfold Hex.Matrix.mulVec Hex.Matrix.dot Hex.Matrix.row Hex.Vector.dotProduct
  rw [Vector.getElem_ofFn i.isLt]
  rw [foldl_finRange_eq_sum]
  unfold _root_.Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro k _
  rfl

private theorem vectorEquiv_nullspaceMatrix_mulVec [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRREF M D) (c : Vector R (m - D.rank)) :
    vectorEquiv (E.nullspaceMatrix * c) =
      ∑ k : Fin (m - D.rank), c[k] • vectorEquiv (E.nullspace.get k) := by
  funext j
  simp only [vectorEquiv_apply, Pi.smul_apply, Finset.sum_apply]
  change (Hex.Matrix.mulVec E.nullspaceMatrix c)[j.val] =
    ∑ k : Fin (m - D.rank), c[k] * (E.nullspace.get k)[j]
  unfold Hex.Matrix.mulVec Hex.Matrix.dot Hex.Matrix.row Hex.Vector.dotProduct
  rw [Vector.getElem_ofFn j.isLt]
  rw [foldl_finRange_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold Hex.Matrix.IsRREF.nullspace Hex.Matrix.col
  simp [mul_comm]

theorem rank_eq [Field R] (M : Hex.Matrix R n m)
    (D : Hex.Matrix.RowEchelonData R n m) (E : Hex.Matrix.IsEchelonForm M D) :
    D.rank = _root_.Matrix.rank (matrixEquiv M) := by
  sorry

theorem spanCoeffs_eq_linearCombination [Field R] [DecidableEq R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsEchelonForm M D) (v : Vector R m) (c : Vector R n) :
    E.spanCoeffs v = some c →
      vectorEquiv v =
        Fintype.linearCombination R (_root_.Matrix.row (matrixEquiv M)) (vectorEquiv c) := by
  sorry

theorem spanContains_iff_mem_span [Field R] [DecidableEq R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsEchelonForm M D) (v : Vector R m) :
    E.spanContains v = true ↔
      vectorEquiv v ∈ Submodule.span R (Set.range (_root_.Matrix.row (matrixEquiv M))) := by
  sorry

theorem nullspace_mem_ker [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRREF M D) (k : Fin (m - D.rank)) :
    vectorEquiv (E.nullspace.get k) ∈
      LinearMap.ker ((_root_.Matrix.mulVecLin (matrixEquiv M))) := by
  rw [LinearMap.mem_ker, _root_.Matrix.mulVecLin_apply]
  have hsound := Hex.Matrix.IsRREF.nullspace_sound E k
  have hbridge := vectorEquiv_mulVec (M := M) (v := E.nullspace.get k)
  rw [hsound] at hbridge
  have hzero : vectorEquiv (0 : Vector R n) = 0 := by
    ext i
    simp
  rw [hzero] at hbridge
  exact hbridge.symm

theorem nullspace_span_eq_ker [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRREF M D) :
    Submodule.span R (Set.range fun k : Fin (m - D.rank) => vectorEquiv (E.nullspace.get k)) =
      LinearMap.ker (_root_.Matrix.mulVecLin (matrixEquiv M)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    exact nullspace_mem_ker E k
  · intro x hx
    rw [LinearMap.mem_ker, _root_.Matrix.mulVecLin_apply] at hx
    let v : Vector R m := vectorEquiv.symm x
    have hMv : M * v = 0 := by
      have hbridge := vectorEquiv_mulVec (M := M) (v := v)
      have hxv : vectorEquiv v = x := by
        simp [v]
      rw [hxv] at hbridge
      have hzero : (matrixEquiv M).mulVec x = 0 := hx
      rw [hzero] at hbridge
      have hzeroVec : vectorEquiv (M * v) = vectorEquiv (0 : Vector R n) := by
        simpa [vectorEquiv] using hbridge
      exact Equiv.injective vectorEquiv hzeroVec
    rcases Hex.Matrix.IsRREF.nullspace_complete E v hMv with ⟨c, hc⟩
    have hxsum :
        x = ∑ k : Fin (m - D.rank), c[k] • vectorEquiv (E.nullspace.get k) := by
      have hlin := vectorEquiv_nullspaceMatrix_mulVec E c
      rw [hc] at hlin
      have hxv : vectorEquiv v = x := by
        simp [v]
      rw [hxv] at hlin
      exact hlin
    rw [hxsum]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ c[k] (Submodule.subset_span ⟨k, rfl⟩)

end HexMatrixMathlib
