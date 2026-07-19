/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib

public section

/-!
# Hadamard's determinant inequality

This file proves the *sharp* Hadamard determinant inequality over an `RCLike` field: the
norm of the determinant of a square matrix is at most the product of the Euclidean (L²)
norms of its columns.

## Main results

* `Matrix.norm_det_le_prod_norm_column`: for `A : Matrix n n 𝕜` with `[RCLike 𝕜]`,
  `‖A.det‖ ≤ ∏ j, √(∑ i, ‖A i j‖ ^ 2)`, the product of the Euclidean lengths of the columns.

This is genuinely sharper than the entrywise bound `Matrix.det_le`
(which gives the crude `n! · xⁿ` estimate). Equality holds exactly when the columns are
pairwise orthogonal.

The proof is the standard QR / Gram-Schmidt route. Writing the columns as vectors of
`EuclideanSpace 𝕜 n`, the Gram-Schmidt orthonormal basis `e` makes the change-of-basis
matrix upper triangular, so
`e.toBasis.det (columns) = ∏ i, ⟪e i, columns i⟫` (`gramSchmidtOrthonormalBasis_det`).
Each factor is bounded by `‖e i‖ * ‖columns i‖ = ‖columns i‖` by Cauchy-Schwarz, and the
determinant with respect to any orthonormal basis has the same norm as the ordinary matrix
determinant because the change of basis between two orthonormal bases is unitary
(`OrthonormalBasis.det_to_matrix_orthonormalBasis`).

This lemma is not currently in Mathlib (only the weak `Matrix.det_le` entrywise bound and
the unrelated `Matrix.IsHadamard` `±1`-matrix theory) and is a natural upstream target. It
is consumed by the real- and complex-root separation developments, where Mahler's
root-separation bound is obtained by applying Hadamard to a Vandermonde matrix.
-/

open Finset Module InnerProductSpace
open scoped InnerProductSpace

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  [LinearOrder n] [LocallyFiniteOrderBot n] [WellFoundedLT n]

/-- **Hadamard's inequality** (sharp form). The norm of the determinant of a square matrix
over an `RCLike` field is at most the product of the Euclidean (L²) norms of its columns:
`‖A.det‖ ≤ ∏ j, √(∑ i, ‖A i j‖ ^ 2)`.

This dominates the crude entrywise bound `Matrix.det_le`; equality holds precisely when the
columns are pairwise orthogonal. -/
theorem norm_det_le_prod_norm_column (A : Matrix n n 𝕜) :
    ‖A.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) := by
  classical
  -- The columns of `A` viewed as vectors of Euclidean space.
  set f : n → EuclideanSpace 𝕜 n :=
    fun j => (WithLp.equiv 2 (n → 𝕜)).symm (fun i => A i j) with hf
  have hfi : ∀ i j, (f j) i = A i j := fun i j => rfl
  -- `‖f j‖` is exactly the L² norm of column `j`.
  have hcol : ∀ j, ‖f j‖ = Real.sqrt (∑ i, ‖A i j‖ ^ 2) := by
    intro j
    rw [EuclideanSpace.norm_eq]
    simp only [hfi]
  -- The Gram-Schmidt orthonormal basis built from the columns.
  have hdim : finrank 𝕜 (EuclideanSpace 𝕜 n) = Fintype.card n := finrank_euclideanSpace
  set e := gramSchmidtOrthonormalBasis hdim f with he
  -- Its change-of-basis determinant is the product of the diagonal inner products.
  have hdet : e.toBasis.det f = ∏ i, inner 𝕜 (e i) (f i) := by
    rw [he]; exact gramSchmidtOrthonormalBasis_det hdim f
  -- The determinant with respect to the standard orthonormal basis is `A.det`.
  have hmat : (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix f = A := by
    ext i j
    rw [Basis.toMatrix_apply, EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr]
    exact hfi i j
  have hstd : (EuclideanSpace.basisFun n 𝕜).toBasis.det f = A.det := by
    rw [Basis.det_apply, hmat]
  -- Passing from `e` to the standard orthonormal basis rescales the determinant by a
  -- unit-modulus factor, so the norms agree.
  have hchange : ‖e.toBasis.det f‖ = ‖A.det‖ := by
    have key : e.toBasis.det f
        = (e.toBasis.det (EuclideanSpace.basisFun n 𝕜).toBasis)
          • ((EuclideanSpace.basisFun n 𝕜).toBasis.det f) := by
      rw [← AlternatingMap.smul_apply]
      congr 1
      exact (e.toBasis.det).eq_smul_basis_det (EuclideanSpace.basisFun n 𝕜).toBasis
    have hunit : ‖e.toBasis.det (EuclideanSpace.basisFun n 𝕜).toBasis‖ = 1 := by
      rw [OrthonormalBasis.coe_toBasis]
      exact e.det_to_matrix_orthonormalBasis (EuclideanSpace.basisFun n 𝕜)
    rw [key, norm_smul, hunit, one_mul, hstd]
  -- Cauchy-Schwarz on each diagonal factor.
  have hbound : ‖e.toBasis.det f‖ ≤ ∏ j, ‖f j‖ := by
    rw [hdet, norm_prod]
    refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
    calc ‖inner 𝕜 (e i) (f i)‖ ≤ ‖e i‖ * ‖f i‖ := norm_inner_le_norm _ _
      _ = ‖f i‖ := by rw [e.orthonormal.norm_eq_one, one_mul]
  calc ‖A.det‖ = ‖e.toBasis.det f‖ := hchange.symm
    _ ≤ ∏ j, ‖f j‖ := hbound
    _ = ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) := Finset.prod_congr rfl (fun j _ => hcol j)

end Matrix
