/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHermite.Contracts
public import HexMatrix.Certificate

public section

/-! Packed, independently checkable certificates for Hermite normal form. -/

namespace Hex.Matrix

/-- Accept `(H,U,W)` as HNF data for `A`, checking one transform product,
one inverse product, and every entry-level HNF clause. -/
@[expose]
def hnfCert (A H : Matrix Int n m) (U W : Matrix Int n n)
    (r : Nat) (piv : Vector (Fin m) r) : Bool :=
  Matrix.mulEqCert U A H &&
    Matrix.mulEqCert U W (Matrix.identity n) &&
    isHNFForm H r piv

/-- Every accepted HNF certificate establishes the full HNF contract. -/
theorem hnfCert_sound {A H : Matrix Int n m} {U W : Matrix Int n n}
    {r : Nat} {piv : Vector (Fin m) r} :
    hnfCert A H U W r piv = true → IsHNF A ⟨r, H, U, piv⟩ := by
  intro hcert
  simp only [hnfCert, Bool.and_eq_true, Matrix.mulEqCert_iff,
    isHNFForm_iff] at hcert
  have hUA := hcert.1.1
  have hUW := hcert.1.2
  have hshape := hcert.2
  have hrn := hshape.1
  have hrm := hshape.2.1
  have hsorted := hshape.2.2.1
  have hleading := hshape.2.2.2.1
  have hpos := hshape.2.2.2.2.1
  have hbelow := hshape.2.2.2.2.2.1
  have hzero := hshape.2.2.2.2.2.2.1
  have hnonneg := hshape.2.2.2.2.2.2.2.1
  have hlt := hshape.2.2.2.2.2.2.2.2
  have hWU : W * U = Matrix.identity n := mul_eq_one_comm hUW
  let pivotRow : Fin r → Fin n := fun i =>
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt hrn⟩
  refine
    { toIsEchelonForm :=
        { transform_mul := hUA
          transform_inv := ⟨W, hWU⟩
          transform_right_inv := ⟨W, hUW⟩
          rank_le_n := hrn
          rank_le_m := hrm
          pivotCols_sorted := hsorted
          below_pivot_zero := ?_
          zero_row := hzero }
      pivot_leading := ?_
      pivot_pos := ?_
      above_nonneg := ?_
      above_lt := ?_ }
  · intro i row hir
    change (H.getRow row).get (piv.get i) = 0
    simpa only [Matrix.getElem_pair_eq_get] using hbelow i row hir
  · intro i j hj
    change (H.getRow (pivotRow i)).get j = 0
    simpa only [Matrix.getElem_pair_eq_get] using hleading i (pivotRow i) rfl j hj
  · intro i
    change 0 < (H.getRow (pivotRow i)).get (piv.get i)
    simpa only [Matrix.getElem_pair_eq_get] using hpos i (pivotRow i) rfl
  · intro i row hir
    change 0 ≤ (H.getRow row).get (piv.get i)
    simpa only [Matrix.getElem_pair_eq_get] using hnonneg i row hir
  · intro i row hir
    change (H.getRow row).get (piv.get i) <
      (H.getRow (pivotRow i)).get (piv.get i)
    simpa only [Matrix.getElem_pair_eq_get] using hlt i row hir (pivotRow i) rfl

end Hex.Matrix
