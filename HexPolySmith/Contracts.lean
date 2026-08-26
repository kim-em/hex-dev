/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly
public import HexMatrix
public import HexDeterminant

public section

/-!
Data and logical contracts for polynomial Smith normal form.
-/

namespace Hex.PolyMatrix

universe u

open Hex

/-- Executable Smith normal form data over `F[x]`: the rank, invariant
factors, and both change-of-basis matrices with their inverses. -/
structure SmithData (F : Type u) [Zero F] [DecidableEq F] (n m : Nat) where
  /-- Number of nonzero Smith diagonal entries. -/
  rank : Nat
  /-- Monic nonzero invariant factors, in divisibility order. -/
  diag : Vector (DensePoly F) rank
  /-- Left change-of-basis matrix. -/
  left : Matrix (DensePoly F) n n
  /-- Explicit inverse of the left change-of-basis matrix. -/
  leftInv : Matrix (DensePoly F) n n
  /-- Right change-of-basis matrix. -/
  right : Matrix (DensePoly F) m m
  /-- Explicit inverse of the right change-of-basis matrix. -/
  rightInv : Matrix (DensePoly F) m m

/-- Smith normal form contract over `F[x]`. -/
structure IsSNF {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (S : SmithData F n m) : Prop where
  /-- The stored left inverse is correct. -/
  left_inv : S.left * S.leftInv = Matrix.identity n
  /-- The stored right inverse is correct. -/
  right_inv : S.right * S.rightInv = Matrix.identity m
  /-- The transformations carry the input to the stored Smith diagonal. -/
  mul_eq : S.left * A * S.right = Matrix.diagMatrix S.diag n m
  /-- The rank does not exceed the row count. -/
  rank_le_n : S.rank ≤ n
  /-- The rank does not exceed the column count. -/
  rank_le_m : S.rank ≤ m
  /-- Every stored invariant factor is monic. -/
  diag_monic : ∀ i : Fin S.rank, S.diag[i].Monic
  /-- Consecutive invariant factors form a divisibility chain. -/
  chain : ∀ (i : Nat) (h : i + 1 < S.rank),
    S.diag[i]'(by omega) ∣ S.diag[i + 1]

/-- Decidable reflection of the rank bounds, monicity, and divisibility chain
in the Smith shape. Product identities are checked separately by `snfCert`. -/
@[expose]
def isSNFShape {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (S : SmithData F n m) : Bool :=
  decide (S.rank ≤ n) && decide (S.rank ≤ m)
    && S.diag.toList.all (fun p => p.leadingCoeff == 1)
    && (S.diag.toList.zip S.diag.toList.tail).all
      (fun q => (q.2 % q.1).isZero)

/-- Soundness of the decidable Smith-shape reflection. -/
theorem isSNFShape_sound {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} {S : SmithData F n m} (h : isSNFShape S = true) :
    S.rank ≤ n ∧ S.rank ≤ m ∧
      (∀ i : Fin S.rank, S.diag[i].Monic) ∧
      (∀ (i : Nat) (hi : i + 1 < S.rank),
        S.diag[i]'(by omega) ∣ S.diag[i + 1]) := by
  simp only [isSNFShape, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hrn, hrm⟩, hmonic⟩, hchain⟩
  refine ⟨of_decide_eq_true hrn, of_decide_eq_true hrm, ?_, ?_⟩
  · intro i
    have hmem : S.diag[i] ∈ S.diag.toList := by
      simp
    have hi := (List.all_eq_true.mp hmonic) S.diag[i] hmem
    exact eq_of_beq hi
  · intro i hi
    have hlt : i < (S.diag.toList.zip S.diag.toList.tail).length := by
      simp
      omega
    have hmem := @List.getElem_mem _
      (S.diag.toList.zip S.diag.toList.tail) i hlt
    have hp := (List.all_eq_true.mp hchain)
      (S.diag.toList.zip S.diag.toList.tail)[i] hmem
    have hp' : (S.diag[i + 1] % S.diag[i]'(by omega)).isZero = true := by
      simpa using hp
    apply DensePoly.dvd_of_mod_eq_zero
    apply (DensePoly.size_eq_zero_iff _).mp
    exact (DensePoly.isZero_eq_true_iff _).mp hp'

/-- The left change-of-basis matrix of Smith data has a unit determinant. -/
theorem IsSNF.left_unit {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} {A : Matrix (DensePoly F) n m} {S : SmithData F n m}
    (h : IsSNF A S) : (Matrix.det S.left).size = 1 := by
  apply DensePoly.size_eq_one_of_mul_eq_one
    (Matrix.det S.left) (Matrix.det S.leftInv)
  rw [← Matrix.det_mul, h.left_inv, Matrix.det_identity]

/-- The right change-of-basis determinant is a nonzero constant. -/
theorem IsSNF.right_unit {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} {A : Matrix (DensePoly F) n m} {S : SmithData F n m}
    (h : IsSNF A S) :
    ∃ c : F, c ≠ 0 ∧ Matrix.det S.right = DensePoly.C c := by
  have hsize : (Matrix.det S.right).size = 1 := by
    apply DensePoly.size_eq_one_of_mul_eq_one
      (Matrix.det S.right) (Matrix.det S.rightInv)
    rw [← Matrix.det_mul, h.right_inv, Matrix.det_identity]
  refine ⟨(Matrix.det S.right).leadingCoeff, ?_,
    DensePoly.eq_C_leadingCoeff_of_size_one hsize⟩
  apply DensePoly.leadingCoeff_ne_zero_of_pos_size
  omega

end Hex.PolyMatrix
