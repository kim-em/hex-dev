/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHermite.Contracts
public import HexMatrix.Diagonal

public section

/-! Data and contracts for Smith normal form over the integers. -/

namespace Hex.Matrix

/-- Executable Smith-normal-form data: the rank, invariant factors, and both
changes of basis together with explicitly accumulated right inverses. -/
structure SmithData (n m : Nat) where
  /-- Number of nonzero invariant factors. -/
  rank : Nat
  /-- Positive invariant factors in divisibility-chain order. -/
  diag : Vector Int rank
  /-- Left unimodular transform. -/
  left : Matrix Int n n
  /-- Explicit inverse of the left transform. -/
  leftInv : Matrix Int n n
  /-- Right unimodular transform. -/
  right : Matrix Int m m
  /-- Explicit inverse of the right transform. -/
  rightInv : Matrix Int m m

/-- Named structure-theorem data for the quotient of `ℤᵐ` by the row lattice
of a presentation matrix. -/
structure AbelianStructure where
  /-- Rank of the free summand. -/
  freeRank : Nat
  /-- Non-unit torsion invariant factors in divisibility-chain order. -/
  torsionFactors : Array Nat
  deriving Repr, DecidableEq

/-- The Smith-normal-form contract for an integer matrix. -/
structure IsSNF {n m : Nat} (A : Matrix Int n m) (S : SmithData n m) : Prop where
  /-- The recorded left matrices are inverses. -/
  left_inv : S.left * S.leftInv = Matrix.identity n
  /-- The recorded right matrices are inverses. -/
  right_inv : S.right * S.rightInv = Matrix.identity m
  /-- The transforms carry the input to its recorded Smith diagonal. -/
  mul_eq : S.left * A * S.right = diagMatrix S.diag n m
  /-- The reported rank does not exceed the row count. -/
  rank_le_n : S.rank ≤ n
  /-- The reported rank does not exceed the column count. -/
  rank_le_m : S.rank ≤ m
  /-- Every recorded invariant factor is positive. -/
  diag_pos : ∀ i : Fin S.rank, 0 < S.diag[i]
  /-- Consecutive invariant factors form a divisibility chain. -/
  chain : ∀ (i : Nat) (h : i + 1 < S.rank),
    S.diag[(⟨i, by omega⟩ : Fin S.rank)] ∣ S.diag[(⟨i + 1, h⟩ : Fin S.rank)]

/-- The decidable, transform-independent shape clauses of Smith data. -/
@[expose]
def SNFShape {n m : Nat} (S : SmithData n m) : Prop :=
  S.rank ≤ n ∧
  S.rank ≤ m ∧
  (∀ i : Fin S.rank, 0 < S.diag[i]) ∧
  (∀ i : Fin (S.rank - 1),
    S.diag[(⟨i.val, by omega⟩ : Fin S.rank)] ∣
      S.diag[(⟨i.val + 1, by omega⟩ : Fin S.rank)])

instance {n m : Nat} (S : SmithData n m) : Decidable (SNFShape S) := by
  unfold SNFShape
  infer_instance

/-- Decide the rank bounds, positivity, and divisibility chain of Smith data. -/
@[expose]
def isSNFShape {n m : Nat} (S : SmithData n m) : Bool :=
  decide (SNFShape S)

/-- Boolean shape checking agrees with the logical shape predicate. -/
@[simp]
theorem isSNFShape_iff {n m : Nat} (S : SmithData n m) :
    isSNFShape S = true ↔ SNFShape S := by
  simp [isSNFShape]

end Hex.Matrix
