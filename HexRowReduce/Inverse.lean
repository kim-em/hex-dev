/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduce.Api

public section

namespace Hex.Matrix

universe u
variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F] {n : Nat}

/-- Invert a square matrix by reducing its coefficient block and accumulating
the same row operations on the identity. Failure means singularity. -/
@[expose]
def inverse? (A : Matrix F n n) : Option (Matrix F n n) :=
  let D := rowReduce A
  if D.rank = n then some D.transform else none

/-- Inversion succeeds exactly at full rank. -/
theorem inverse?_isSome (A : Matrix F n n) :
    (inverse? A).isSome ↔ rowReduce_rank A = n := by
  simp [inverse?, rowReduce_rank]

/-- Inversion fails exactly when the matrix is rank deficient. -/
theorem inverse?_eq_none (A : Matrix F n n) :
    inverse? A = none ↔ rowReduce_rank A ≠ n := by
  simp [inverse?, rowReduce_rank]

/-- The returned matrix is a two-sided inverse. -/
theorem inverse?_spec (A B : Matrix F n n) :
    inverse? A = some B →
      A * B = Matrix.identity n ∧ B * A = Matrix.identity n := by
  intro h
  unfold inverse? at h
  dsimp only at h
  split at h
  next hr =>
    cases Option.some.inj h
    let E := rowReduce_isRowReduced A
    have he : (rowReduce A).echelon = Matrix.identity n := by
      have ht := rowReduce_head_identity A (Nat.le_refl n) hr
      apply Matrix.ext_getElem
      intro i j
      simpa only [getElem_takeRows] using
        congrArg (fun M : Matrix F n n => M[i][j]) ht
    have hleft : (rowReduce A).transform * A = Matrix.identity n :=
      E.transform_mul.trans he
    obtain ⟨T, hT⟩ := E.transform_inv
    have hA : A = T := by
      calc
        A = Matrix.identity n * A := (identity_mul A).symm
        _ = (T * (rowReduce A).transform) * A := by rw [hT]
        _ = T * ((rowReduce A).transform * A) := mul_assoc _ _ _
        _ = T := by rw [hleft, mul_identity]
    exact ⟨by calc
      A * (rowReduce A).transform = T * (rowReduce A).transform :=
        congrArg (fun X => X * (rowReduce A).transform) hA
      _ = Matrix.identity n := hT, hleft⟩
  next => contradiction

/-- The empty matrix has the empty identity as its inverse. -/
theorem inverse?_empty (A : Matrix F 0 0) :
    inverse? A = some (Matrix.identity 0) := by
  have hr : (rowReduce A).rank = 0 := Nat.eq_zero_of_le_zero (rowReduce_isRowReduced A).rank_le_n
  unfold inverse?
  dsimp only
  rw [ite_eq_left hr]
  congr 1
  apply Matrix.ext_getElem
  intro i j
  exact Fin.elim0 i

end Hex.Matrix
