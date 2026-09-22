/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Tensor
public import HexRankMathlib.Sound
public import Mathlib.LinearAlgebra.Matrix.Kronecker

public section

namespace Hex.SignDet

open HexMatrixMathlib
open scoped Kronecker

/-- The dimension-indexed product is exactly the existing ordered list
product used by the recursive checker, rather than a permutation of it. -/
theorem productVector_toList {r s : Nat} (xs : Vector (List α) r) (ys : Vector (List α) s) :
    (productVector xs ys).toList = product xs.toList ys.toList := by
  have hv {n : Nat} (v : Vector (List α) n) :
      v.toList = List.ofFn (fun i : Fin n => v[i]) := by
    rw [← Vector.toList_ofFn]
    simp only [Fin.getElem_fin, Vector.ofFn_getElem]
  rw [productVector, Vector.toList_ofFn, List.ofFn_mul]
  simp only [Fin.getElem_fin]
  rw [product, List.flatMap_def, hv xs, hv ys]
  simp only [List.map_ofFn, Function.comp_def, Fin.getElem_fin]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simp only [Matrix.flatIdx_div j.isLt, Matrix.flatIdx_mod j.isLt]

/-- Concatenated exponent/sign entries form the exact tensor matrix in the
existing ordered supports. The length premise prevents zip truncation. -/
theorem momentMatrix_product {r s : Nat} (er : Vector (List Nat) r) (es : Vector (List Nat) s)
    (cr : Vector (List Int) r) (cs : Vector (List Int) s)
    (hlen : ∀ i j : Fin r, er[i].length = cr[j].length) :
    momentMatrix (productVector er es) (productVector cr cs) =
      tensor (momentMatrix er cr) (momentMatrix es cs) := by
  apply Matrix.ext_getElem
  intro i j
  simp only [momentMatrix, tensor, Matrix.getElem_pair_eq_nested, Matrix.getElem_ofFn]
  simp only [productVector, Fin.getElem_fin, Vector.getElem_ofFn]
  exact entry_append _ _ _ _
    (hlen ⟨i.val / s, Matrix.row_of_lt i⟩ ⟨j.val / s, Matrix.row_of_lt j⟩)

/-- The executable tensor uses the standard product indexing, with the right
coordinate varying fastest. This includes zero-dimensional factors. -/
theorem matrixEquiv_tensor {r s : Nat} (a : Matrix Int r r) (b : Matrix Int s s) :
    matrixEquiv (tensor a b) = (matrixEquiv a ⊗ₖ matrixEquiv b).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm := by
  ext i j
  simp only [tensor, matrixEquiv_apply, Matrix.getElem_ofFn]
  rfl

/-- Tensor construction preserves the exact matrix multiplication used by
the integer replay identities. -/
theorem tensor_mul {r s : Nat} (a c : Matrix Int r r) (b d : Matrix Int s s) :
    tensor (a * c) (b * d) = tensor a b * tensor c d := by
  apply matrixEquiv.injective
  simp only [matrixEquiv_tensor, matrixEquiv_mul]
  rw [_root_.Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm,
    _root_.Matrix.mul_kronecker_mul]

/-- Scaling each identity multiplies the common integer denominator. -/
theorem tensor_identity (r s : Nat) (d e : Int) :
    tensor (Matrix.scale d (Matrix.identity r)) (Matrix.scale e (Matrix.identity s)) =
      Matrix.scale (d * e) (Matrix.identity (r * s)) := by
  apply matrixEquiv.injective
  simp only [matrixEquiv_tensor, Matrix.scale_eq_smul, matrixEquiv_smul, matrixEquiv_identity,
    _root_.Matrix.smul_kronecker, _root_.Matrix.kronecker_smul,
    _root_.Matrix.one_kronecker_one, smul_smul]
  ext i j
  simp only [_root_.Matrix.submatrix_apply, _root_.Matrix.smul_apply, _root_.Matrix.one_apply,
    smul_eq_mul, (finProdFinEquiv : Fin r × Fin s ≃ Fin (r * s)).symm.injective.eq_iff,
    mul_comm e d]

/-- Child scaled left inverses compose without a new rational inversion. -/
theorem tensor_inverse {r s : Nat} (a ai : Matrix Int r r) (b bi : Matrix Int s s)
    (d e : Int) (ha : ai * a = Matrix.scale d (Matrix.identity r))
    (hb : bi * b = Matrix.scale e (Matrix.identity s)) :
    tensor ai bi * tensor a b = Matrix.scale (d * e) (Matrix.identity (r * s)) := by
  rw [← tensor_mul, ha, hb, tensor_identity]

end Hex.SignDet
