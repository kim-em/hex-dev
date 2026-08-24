/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHermite
public import HexMatrixMathlib.Algebra
public import HexRowReduceMathlib.RankSpanNullspace
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

public section

/-! Mathlib correspondence for integer row lattices and the HNF transform. -/

namespace HexHermiteMathlib

open HexMatrixMathlib

/-- The executable row-vector product agrees with Mathlib's linear map. -/
theorem vectorEquiv_vecMulLinear (A : Hex.Matrix Int n m) (c : Vector Int n) :
    vectorEquiv (Hex.Matrix.vecMul c A) =
      (_root_.Matrix.vecMulLinear (matrixEquiv A)) (vectorEquiv c) := by
  rw [vectorEquiv_vecMul, _root_.Matrix.vecMulLinear_apply,
    Fintype.linearCombination_apply, _root_.Matrix.vecMul_eq_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

/-- Executable integer row-lattice membership is membership in the Mathlib
span of the rows. -/
theorem mem_span_iff (A : Hex.Matrix Int n m) (v : Vector Int m) :
    vectorEquiv v ∈
        Submodule.span ℤ (Set.range (_root_.Matrix.row (matrixEquiv A))) ↔
      A.memLattice v := by
  unfold Hex.Matrix.memLattice
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨vectorEquiv.symm c, vectorEquiv.injective ?_⟩
    rw [vectorEquiv_vecMul, Fintype.linearCombination_apply,
      Equiv.apply_symm_apply]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hc
    rw [matrixEquiv_row]
  · rintro ⟨c, hc⟩
    refine ⟨vectorEquiv c, ?_⟩
    have hrow := vectorEquiv_vecMul A c
    rw [hc, Fintype.linearCombination_apply] at hrow
    rw [hrow]

/-- Hermite reduction preserves the Mathlib row span. -/
theorem span_hnf (A : Hex.Matrix Int n m) :
    Submodule.span ℤ
        (Set.range (_root_.Matrix.row (matrixEquiv (Hex.Matrix.hnf A)))) =
      Submodule.span ℤ (Set.range (_root_.Matrix.row (matrixEquiv A))) := by
  ext x
  let v : Vector Int m := vectorEquiv.symm x
  have hv : vectorEquiv v = x := Equiv.apply_symm_apply vectorEquiv x
  rw [← hv, mem_span_iff, mem_span_iff]
  exact (Hex.Matrix.hnf_memLattice_iff A v).symm

/-- The accumulated Hermite row transform is invertible over `ℤ`. -/
theorem isUnit_transform (A : Hex.Matrix Int n m) :
    IsUnit (matrixEquiv (Hex.Matrix.hnfData A).transform) := by
  let D := Hex.Matrix.hnfWithInv A
  have hdata := Hex.Matrix.hnfWithInv_data A
  have htransform : (Hex.Matrix.hnfData A).transform = D.rowData.transform :=
    congrArg Hex.Matrix.RowEchelonData.transform hdata.symm
  refine isUnit_iff_exists.mpr ⟨matrixEquiv D.inverse, ?_, ?_⟩
  · rw [htransform, ← matrixEquiv_mul, Hex.Matrix.hnfWithInv_mul_inv]
    change matrixEquiv (1 : Hex.Matrix Int n n) = 1
    exact matrixEquiv_one
  · rw [htransform, ← matrixEquiv_mul, Hex.Matrix.hnfWithInv_inv_mul]
    change matrixEquiv (1 : Hex.Matrix Int n n) = 1
    exact matrixEquiv_one

/-- Executable lattice membership agrees with membership in the Mathlib row
span. -/
theorem latticeContains_iff_mem (A : Hex.Matrix Int n m) (v : Vector Int m) :
    Hex.Matrix.latticeContains A v = true ↔
      vectorEquiv v ∈
        Submodule.span ℤ (Set.range (_root_.Matrix.row (matrixEquiv A))) := by
  rw [Hex.Matrix.latticeContains_iff, mem_span_iff]
  rfl

end HexHermiteMathlib
