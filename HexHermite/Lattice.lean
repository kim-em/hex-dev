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

set_option maxHeartbeats 400000 in
private theorem recover_of_inverse {A : Matrix Int n m} {H : Matrix Int n m}
    {U W : Matrix Int n n} (hUA : U * A = H)
    (hWU : W * U = Matrix.identity (R := Int) n) : W * H = A := by
  calc
    W * H = W * (U * A) := by rw [hUA]
    _ = (W * U) * A := (Matrix.mul_assoc W U A).symm
    _ = Matrix.identity (R := Int) n * A := by rw [hWU]
    _ = A := Matrix.identity_mul A

set_option maxHeartbeats 400000 in
/-- Hermite reduction preserves the integer row lattice. -/
theorem hnf_memLattice_iff (A : Matrix Int n m) (v : Vector Int m) :
    A.memLattice v ↔ (hnf A).memLattice v := by
  let D := hnfWithInv A
  have hforward : D.rowData.transform * A = D.rowData.echelon :=
    hnfWithInv_transform_mul A
  have hback : D.inverse * D.rowData.echelon = A :=
    recover_of_inverse hforward (hnfWithInv_inv_mul A)
  have hform : hnf A = D.rowData.echelon := by
    rw [hnf_eq_hnfData_echelon, ← hnfWithInv_data A]
  rw [hform]
  exact memLattice_iff_of_mul_eq hforward hback v

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

/-- The returned kernel rows are annihilated by the input matrix. -/
theorem kernelBasis_mul (A : Matrix Int n m) : kernelBasis A * A = 0 := by
  let D := hnfData A
  have hform := hnfData_isHNF A
  have hrank : hnfRank A = D.rank := hnfRank_eq A
  apply Matrix.ext_getElem
  intro i j
  let row : Fin n := ⟨hnfRank A + i.val, by
    have hr := hform.toIsEchelonForm.rank_le_n
    omega⟩
  have hrow : D.rank ≤ row.val := by simp only [row]; omega
  have hzero : D.echelon[row] = 0 := hform.toIsEchelonForm.zero_row row hrow
  calc
    (kernelBasis A * A)[i][j] = (D.transform * A)[row][j] := by
      simp only [D, row, Matrix.getElem_mul, kernelBasis, Matrix.getElem_ofFn,
        Matrix.getElem_row, Matrix.getElem_col, Matrix.getElem_pair_eq_nested,
        Vector.dotProduct]
    _ = D.echelon[row][j] := by rw [hnfData_transform_mul A]
    _ = 0 := by rw [hzero]; simp
    _ = (0 : Matrix Int (n - hnfRank A) m)[i][j] :=
      (Matrix.getElem_zero i j).symm

@[simp] theorem latticeContains_eq_isSome (A : Matrix Int n m) (v : Vector Int m) :
    latticeContains A v = (latticeCoeffs A v).isSome := rfl

/-- The index definition is the pivot product in the full-rank case. -/
theorem latticeIndex_eq_prod_pivots (A : Matrix Int n m) (h : hnfRank A = m) :
    latticeIndex A = (pivots A).foldl (· * ·) 1 := by
  simp [latticeIndex, h]

end Hex.Matrix
