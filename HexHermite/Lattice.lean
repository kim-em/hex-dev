/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHermite.Hermite
public import HexMatrix.Lattice

public section

/-! Executable row-lattice, kernel, pivot, and index APIs derived from HNF. -/

namespace Hex.Matrix

namespace Hermite

/-- Solve against the nonzero HNF rows by forward pivot substitution. -/
@[expose]
def solve (H : Matrix Int n m) (r : Nat) (piv : Vector (Fin m) r)
    (v : Vector Int m) : Option (Vector Int n) :=
  let initial : Vector Int m × Vector Int n := (v, 0)
  let result := (List.finRange n).foldlM (m := Option)
    (fun (state : Vector Int m × Vector Int n) (row : Fin n) =>
      if hr : row.val < r then
        let i : Fin r := ⟨row.val, hr⟩
        let col := piv.get i
        let p : Int := H[(row, col)]
        if p = 0 then
          none
        else
          let value := state.1.get col
          if value % p = 0 then
            let q := value / p
            let residual := Vector.ofFn fun j => state.1.get j - q * H[(row, j)]
            some (residual, state.2.set row.val q row.isLt)
          else
            none
      else
        some state) initial
  match result with
  | none => none
  | some (residual, coeffs) =>
      if residual = 0 then some coeffs else none

end Hermite

/-- Integer coefficients expressing `v` as a combination of the rows of
`A`, or `none` when the forward HNF solve does not verify. -/
@[expose]
def latticeCoeffs (A : Matrix Int n m) (v : Vector Int m) : Option (Vector Int n) :=
  let D := hnfData A
  match Hermite.solve D.echelon D.rank D.pivotCols v with
  | none => none
  | some d =>
      let c := Matrix.transpose D.transform * d
      if vecMul c A = v then some c else none

/-- Decide membership in the integer row lattice of `A`. -/
@[expose]
def latticeContains (A : Matrix Int n m) (v : Vector Int m) : Bool :=
  (latticeCoeffs A v).isSome

/-- The rows of the transform corresponding to zero HNF rows. -/
@[expose]
def kernelBasis (A : Matrix Int n m) : Matrix Int (n - hnfRank A) n :=
  let hr := Hermite.run_rank_le (Hermite.formAccumulator n) A
  Matrix.ofFn fun i j =>
    let row : Fin n := ⟨hnfRank A + i.val, by omega⟩
    (hnfData A).transform[(row, j)]

/-- Positive HNF pivot values in pivot-column order. -/
@[expose]
def pivots (A : Matrix Int n m) : Vector Nat (hnfRank A) :=
  let D := hnfData A
  let hrank := hnfRank_eq A
  let hr := Hermite.run_rank_le (Hermite.transformAccumulator n) A
  have hrD : D.rank ≤ n := by
    change (Hermite.run (Hermite.transformAccumulator n) A).pivots.length ≤ n
    exact hr
  Vector.ofFn fun i =>
    have hiD : i.val < D.rank := by
      rw [← hrank]
      exact i.isLt
    let pi : Fin D.rank := ⟨i.val, hiD⟩
    let row : Fin n := ⟨i.val, Nat.lt_of_lt_of_le hiD hrD⟩
    (D.echelon[(row, D.pivotCols.get pi)]).natAbs

/-- Index of the row lattice in `Int^m`, with `0` denoting infinite index. -/
@[expose]
def latticeIndex (A : Matrix Int n m) : Nat :=
  if hnfRank A = m then
    (pivots A).foldl (· * ·) 1
  else
    0

/-- Every returned lattice coefficient vector satisfies its advertised
row-combination equation. -/
theorem latticeCoeffs_sound {A : Matrix Int n m} {v : Vector Int m}
    {c : Vector Int n} :
    latticeCoeffs A v = some c → vecMul c A = v := by
  intro h
  unfold latticeCoeffs at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · rename_i d hverify
      injection h with hc
      subst c
      exact hverify
    · contradiction

@[simp] theorem latticeContains_eq_isSome (A : Matrix Int n m) (v : Vector Int m) :
    latticeContains A v = (latticeCoeffs A v).isSome := rfl

/-- The index definition is the pivot product in the full-rank case. -/
theorem latticeIndex_eq_prod_pivots (A : Matrix Int n m) (h : hnfRank A = m) :
    latticeIndex A = (pivots A).foldl (· * ·) 1 := by
  simp [latticeIndex, h]

end Hex.Matrix
