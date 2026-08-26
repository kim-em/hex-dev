/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSmith.Contracts
public import HexMatrix.Certificate

public section

/-! Independently checkable certificates for Smith normal form. -/

namespace Hex.Matrix

/-- Accept `(S,T)` as Smith data for `A`, where `T = S.left * A` is supplied
to keep the checker from allocating either full product internally. -/
@[expose]
def snfCert (A : Matrix Int n m) (S : SmithData n m) (T : Matrix Int n m) : Bool :=
  Matrix.mulEqCert S.left A T &&
    Matrix.mulEqCert S.right.transpose T.transpose
      (diagMatrix S.diag n m).transpose &&
    Matrix.mulEqCert S.left S.leftInv (Matrix.identity n) &&
    Matrix.mulEqCert S.right S.rightInv (Matrix.identity m) &&
    isSNFShape S

/-- Every accepted Smith certificate establishes the full Smith contract. -/
theorem snfCert_sound {A : Matrix Int n m} {S : SmithData n m}
    {T : Matrix Int n m} :
    snfCert A S T = true → IsSNF A S := by
  intro hcert
  simp only [snfCert, Bool.and_eq_true, Matrix.mulEqCert_iff,
    isSNFShape_iff] at hcert
  have hleft := hcert.1.1.1.1
  have hrightTranspose := hcert.1.1.1.2
  have hleftInv := hcert.1.1.2
  have hrightInv := hcert.1.2
  have hshape := hcert.2
  have hright : T * S.right = diagMatrix S.diag n m := by
    have h := congrArg Matrix.transpose hrightTranspose
    simpa only [Matrix.transpose_mul_of_mul_comm, Matrix.transpose_transpose] using h
  refine
    { left_inv := hleftInv
      right_inv := hrightInv
      mul_eq := ?_
      rank_le_n := hshape.1
      rank_le_m := hshape.2.1
      diag_pos := hshape.2.2.1
      chain := ?_ }
  · rw [hleft, hright]
  · intro i hi
    let ii : Fin (S.rank - 1) := ⟨i, by omega⟩
    exact hshape.2.2.2 ii

end Hex.Matrix
