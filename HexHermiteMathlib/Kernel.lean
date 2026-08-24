/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHermiteMathlib.Span
public import Mathlib.LinearAlgebra.Basis.Basic

public section

/-! Mathlib interpretation of the saturated integer kernel basis. -/

namespace HexHermiteMathlib

open HexMatrixMathlib
open Module

abbrev leftKernel (A : Hex.Matrix Int n m) :=
  LinearMap.ker (_root_.Matrix.vecMulLinear (matrixEquiv A))

@[simp]
theorem vectorEquiv_zero :
    vectorEquiv (0 : Vector Int n) = (0 : Fin n → Int) := by
  funext i
  simp

/-- A row of the executable kernel basis, regarded as an element of the
Mathlib left kernel. -/
@[expose] def kernelVector (A : Hex.Matrix Int n m)
    (i : Fin (n - Hex.Matrix.hnfRank A)) :
    leftKernel A := by
  refine ⟨vectorEquiv (Hex.Matrix.row (Hex.Matrix.kernelBasis A) i), ?_⟩
  change (_root_.Matrix.vecMulLinear (matrixEquiv A))
    (vectorEquiv (Hex.Matrix.row (Hex.Matrix.kernelBasis A) i)) = 0
  rw [← vectorEquiv_vecMulLinear]
  have hrow := congrArg (fun M => Hex.Matrix.row M i)
    (Hex.Matrix.kernelBasis_mul A)
  rw [Hex.Matrix.row_mul_eq_vecMul] at hrow
  have hz : Hex.Matrix.vecMul
      (Hex.Matrix.row (Hex.Matrix.kernelBasis A) i) A = 0 := by
    rw [hrow, Hex.Matrix.row_zero]
    apply Vector.ext
    intro j hj
    simp
  rw [hz, vectorEquiv_zero]

theorem kernelRows_independent (A : Hex.Matrix Int n m) :
    LinearIndependent ℤ
      (_root_.Matrix.row (matrixEquiv (Hex.Matrix.kernelBasis A))) := by
  rw [← _root_.Matrix.vecMul_injective_iff]
  intro x y hxy
  let c : Vector Int (n - Hex.Matrix.hnfRank A) := vectorEquiv.symm (x - y)
  have hc : Hex.Matrix.vecMul c (Hex.Matrix.kernelBasis A) = 0 := by
    apply vectorEquiv.injective
    rw [vectorEquiv_vecMulLinear]
    rw [show vectorEquiv c = x - y from
      Equiv.apply_symm_apply vectorEquiv (x - y)]
    rw [vectorEquiv_zero]
    simp only [map_sub, _root_.Matrix.vecMulLinear_apply]
    exact sub_eq_zero.mpr hxy
  have czero := Hex.Matrix.kernelBasis_independent hc
  have hsub : x - y = 0 := by
    calc
      x - y = vectorEquiv c := (Equiv.apply_symm_apply vectorEquiv (x - y)).symm
      _ = vectorEquiv 0 := congrArg vectorEquiv czero
      _ = 0 := vectorEquiv_zero
  exact sub_eq_zero.mp hsub

theorem kernelVector_independent (A : Hex.Matrix Int n m) :
    LinearIndependent ℤ (kernelVector A) := by
  apply LinearIndependent.of_comp (leftKernel A).subtype
  change LinearIndependent ℤ
    (fun i => vectorEquiv (Hex.Matrix.row (Hex.Matrix.kernelBasis A) i))
  have hrows :
      (fun i => vectorEquiv (Hex.Matrix.row (Hex.Matrix.kernelBasis A) i)) =
        _root_.Matrix.row (matrixEquiv (Hex.Matrix.kernelBasis A)) := by
    funext i
    exact (matrixEquiv_row (Hex.Matrix.kernelBasis A) i).symm
  rw [hrows]
  exact kernelRows_independent A

theorem kernelVector_spans (A : Hex.Matrix Int n m) :
    ⊤ ≤ Submodule.span ℤ (Set.range (kernelVector A)) := by
  rw [top_le_iff, span_range_eq_top_iff_surjective_fintypeLinearCombination]
  intro x
  let v : Vector Int n := vectorEquiv.symm x.1
  have hv : Hex.Matrix.vecMul v A = 0 := by
    apply vectorEquiv.injective
    rw [vectorEquiv_vecMulLinear]
    rw [show vectorEquiv v = x.1 from Equiv.apply_symm_apply vectorEquiv x.1]
    rw [vectorEquiv_zero]
    exact x.2
  rcases Hex.Matrix.kernelBasis_complete hv with ⟨c, hc⟩
  refine ⟨vectorEquiv c, ?_⟩
  apply (leftKernel A).injective_subtype
  rw [Fintype.linearCombination_apply, map_sum]
  simp_rw [map_smul]
  change (∑ i, vectorEquiv c i •
    vectorEquiv (Hex.Matrix.row (Hex.Matrix.kernelBasis A) i)) = x.1
  calc
    (∑ i, vectorEquiv c i •
        vectorEquiv (Hex.Matrix.row (Hex.Matrix.kernelBasis A) i)) =
        Fintype.linearCombination ℤ
          (_root_.Matrix.row (matrixEquiv (Hex.Matrix.kernelBasis A)))
          (vectorEquiv c) := by
      rw [Fintype.linearCombination_apply]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [matrixEquiv_row]
    _ = vectorEquiv (Hex.Matrix.vecMul c (Hex.Matrix.kernelBasis A)) :=
      (vectorEquiv_vecMul (Hex.Matrix.kernelBasis A) c).symm
    _ = vectorEquiv v := congrArg vectorEquiv hc
    _ = x.1 := Equiv.apply_symm_apply vectorEquiv x.1

/-- The executable rows form a basis of the Mathlib integer left kernel. -/
noncomputable def kernelBasisEquiv (A : Hex.Matrix Int n m) :
    Basis (Fin (n - Hex.Matrix.hnfRank A)) ℤ
      (LinearMap.ker (_root_.Matrix.vecMulLinear (matrixEquiv A))) :=
  Basis.mk (kernelVector_independent A) (kernelVector_spans A)

@[simp]
theorem kernelBasisEquiv_apply (A : Hex.Matrix Int n m)
    (i : Fin (n - Hex.Matrix.hnfRank A)) :
    (kernelBasisEquiv A i : Fin n → Int) =
      vectorEquiv (Hex.Matrix.row (Hex.Matrix.kernelBasis A) i) := by
  rw [kernelBasisEquiv, Basis.mk_apply]
  rfl

end HexHermiteMathlib
