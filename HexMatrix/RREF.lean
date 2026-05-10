import Std
import Batteries.Data.Vector.Lemmas
import HexMatrix.RowEchelon

/-!
Executable RREF, row-span, and nullspace routines for `hex-matrix`.

This module implements a simple Gaussian-elimination-based `rref` routine over
decidable fields, then exposes the row-span and nullspace APIs layered on top of
the resulting echelon data. It also states the theorem surface connecting the
computed data to the `IsRREF` contract and the derived span/nullspace
characterizations.
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n m : Nat}

/-- A linear combination of the rows of `M`, using coefficients `c`. -/
def rowCombination [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (c : Vector R n) :
    Vector R m :=
  Matrix.transpose M * c

private structure RrefState (R : Type u) (n m : Nat) where
  row : Nat
  echelon : Matrix R n m
  transform : Matrix R n n
  pivots : List (Fin m)

section FieldAlgorithms

variable [Lean.Grind.Field R] [DecidableEq R]

/-- Search for a nonzero pivot in `col`, starting at row `start`. -/
private def findPivotAux (M : Matrix R n m) (col : Fin m) (start fuel : Nat) :
    Option (Fin n) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : start < n then
        let i : Fin n := ⟨start, h⟩
        if M[i][col] = 0 then
          findPivotAux M col (start + 1) fuel
        else
          some i
      else
        none

/-- Search for a nonzero pivot in `col`, starting at row `start`. -/
private def findPivot? (M : Matrix R n m) (col : Fin m) (start : Nat) : Option (Fin n) :=
  findPivotAux M col start (n - start)

/-- Eliminate every non-pivot entry in a pivot column. -/
private def eliminateColumn (M : Matrix R n m) (T : Matrix R n n)
    (pivotRow : Fin n) (col : Fin m) : Matrix R n m × Matrix R n n :=
  (List.finRange n).foldl
    (fun (state : Matrix R n m × Matrix R n n) j =>
      if h : j = pivotRow then
        state
      else
        let coeff := -state.1[j][col]
        if coeff = 0 then
          state
        else
          (rowAdd state.1 pivotRow j coeff, rowAdd state.2 pivotRow j coeff))
    (M, T)

/-- Process columns left-to-right, performing Gauss-Jordan elimination. -/
private def rrefLoop (col fuel : Nat) (state : RrefState R n m) : RrefState R n m :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hRow : state.row < n then
        if hCol : col < m then
          let colFin : Fin m := ⟨col, hCol⟩
          match findPivot? state.echelon colFin state.row with
          | none =>
              rrefLoop (col + 1) fuel state
          | some pivot =>
              let target : Fin n := ⟨state.row, hRow⟩
              let swappedEchelon := rowSwap state.echelon target pivot
              let swappedTransform := rowSwap state.transform target pivot
              let pivotVal := swappedEchelon[target][colFin]
              let scaledEchelon := rowScale swappedEchelon target pivotVal⁻¹
              let scaledTransform := rowScale swappedTransform target pivotVal⁻¹
              let eliminated := eliminateColumn scaledEchelon scaledTransform target colFin
              let nextState : RrefState R n m :=
                { row := state.row + 1
                  echelon := eliminated.1
                  transform := eliminated.2
                  pivots := state.pivots.concat colFin }
              rrefLoop (col + 1) fuel nextState
        else
          state
      else
        state

/-- Reduced row echelon form data computed by Gauss-Jordan elimination. -/
def rref (M : Matrix R n m) : RowEchelonData R n m :=
  let final := rrefLoop 0 m
    { row := 0
      echelon := M
      transform := 1
      pivots := [] }
  { rank := final.pivots.length
    echelon := final.echelon
    transform := final.transform
    pivotCols := ⟨final.pivots.toArray, by simpa using final.pivots.length_toArray⟩ }

/-- The computed `rref` data satisfies the `IsRREF` contract. -/
theorem rref_isRREF (M : Matrix R n m) : IsRREF M (rref M) := by
  sorry

end FieldAlgorithms

namespace IsEchelonForm

private theorem rowCombination_transform_transpose [Lean.Grind.CommRing R]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) (e : Vector R n) :
    rowCombination M (Matrix.transpose D.transform * e) =
      rowCombination D.echelon e := by
  unfold rowCombination
  calc
    Matrix.transpose M * (Matrix.transpose D.transform * e) =
        (Matrix.transpose M * Matrix.transpose D.transform) * e := by
          exact (Matrix.mul_assoc_vec (A := Matrix.transpose M)
            (B := Matrix.transpose D.transform) (v := e)).symm
    _ = Matrix.transpose (D.transform * M) * e := by
          rw [← Matrix.transpose_mul_of_mul_comm Lean.Grind.CommSemiring.mul_comm]
    _ = Matrix.transpose D.echelon * e := by
          rw [E.transform_mul]

/-- Converse row-combination transport: an `M`-row-combination witness `c`
yields a `D.echelon`-row-combination witness `Matrix.transpose Tinv * c`,
where `Tinv` is any left inverse of `D.transform`. The proof reuses the
forward transport at the candidate witness. -/
private theorem rowCombination_transformInv_transpose [Lean.Grind.CommRing R]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) {Tinv : Matrix R n n}
    (hTinv : Tinv * D.transform = 1) (c : Vector R n) :
    rowCombination D.echelon (Matrix.transpose Tinv * c) = rowCombination M c := by
  have hcompose :
      Matrix.transpose D.transform * (Matrix.transpose Tinv * c) = c := by
    calc
      Matrix.transpose D.transform * (Matrix.transpose Tinv * c) =
          (Matrix.transpose D.transform * Matrix.transpose Tinv) * c := by
            exact (Matrix.mul_assoc_vec (A := Matrix.transpose D.transform)
              (B := Matrix.transpose Tinv) (v := c)).symm
      _ = Matrix.transpose (Tinv * D.transform) * c := by
            rw [← Matrix.transpose_mul_of_mul_comm Lean.Grind.CommSemiring.mul_comm]
      _ = Matrix.transpose (1 : Matrix R n n) * c := by
            rw [hTinv]
      _ = (1 : Matrix R n n) * c := by
            rw [Matrix.transpose_one]
      _ = c := Matrix.one_mulVec c
  have hforward := E.rowCombination_transform_transpose (e := Matrix.transpose Tinv * c)
  rw [hcompose] at hforward
  exact hforward.symm

/-- Existential converse transport: any `v` in the row span of `M` is also in
the row span of `D.echelon`, with an explicit witness produced from a left
inverse of `D.transform`. -/
private theorem exists_rowCombination_echelon_of_M [Lean.Grind.CommRing R]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) {v : Vector R m}
    (h : ∃ c : Vector R n, rowCombination M c = v) :
    ∃ d : Vector R n, rowCombination D.echelon d = v := by
  rcases h with ⟨c, hc⟩
  rcases E.transform_inv with ⟨Tinv, hTinv⟩
  refine ⟨Matrix.transpose Tinv * c, ?_⟩
  rw [E.rowCombination_transformInv_transpose hTinv c, hc]

variable [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
variable {M : Matrix R n m} {D : RowEchelonData R n m}

/-- Coefficients for expressing `v` in the row span, if the echelon rows solve it. -/
def spanCoeffs [Lean.Grind.Field R] [DecidableEq R] (E : IsEchelonForm M D)
    (v : Vector R m) : Option (Vector R n) :=
  let echelonCoeffs : Vector R n :=
    Vector.ofFn fun i =>
      if h : i.val < D.rank then
        let pi : Fin D.rank := ⟨i.val, h⟩
        v[D.pivotCols.get pi] /
          D.echelon[(IsEchelonForm.pivotRow E pi)][D.pivotCols.get pi]
      else
        0
  let coeffs := Matrix.transpose D.transform * echelonCoeffs
  if rowCombination M coeffs = v then
    some coeffs
  else
    none

/-- Decidable row-span membership test derived from `spanCoeffs`. -/
def spanContains [Lean.Grind.Field R] [DecidableEq R] (E : IsEchelonForm M D)
    (v : Vector R m) : Bool :=
  (E.spanCoeffs v).isSome

/-- `spanCoeffs` returns coefficients whose row combination equals `v`. -/
theorem spanCoeffs_sound [Lean.Grind.Field R] [DecidableEq R]
    (E : IsEchelonForm M D) (_hpiv : E.HasNonzeroPivots) (v : Vector R m)
    (c : Vector R n) :
    E.spanCoeffs v = some c → rowCombination M c = v := by
  intro h
  unfold spanCoeffs at h
  dsimp only at h
  split at h
  · rename_i hspan
    injection h with hc
    subst c
    exact hspan
  · contradiction

/-- Any vector in the row span produces some coefficients via `spanCoeffs`. -/
theorem spanCoeffs_complete [Lean.Grind.Field R] [DecidableEq R]
    (E : IsEchelonForm M D) (hpiv : E.HasNonzeroPivots) (v : Vector R m) :
    (∃ c : Vector R n, rowCombination M c = v) → (E.spanCoeffs v).isSome := by
  sorry

/-- `spanContains` is exactly row-span membership. -/
theorem spanContains_iff [Lean.Grind.Field R] [DecidableEq R]
    (E : IsEchelonForm M D) (hpiv : E.HasNonzeroPivots) (v : Vector R m) :
    E.spanContains v = true ↔ ∃ c : Vector R n, rowCombination M c = v := by
  constructor
  · intro h
    unfold spanContains at h
    cases hCoeffs : E.spanCoeffs v with
    | none =>
        simp [hCoeffs] at h
    | some c =>
        exact ⟨c, E.spanCoeffs_sound hpiv v c hCoeffs⟩
  · intro h
    unfold spanContains
    simpa using E.spanCoeffs_complete hpiv v h

end IsEchelonForm

namespace IsRREF

/-- RREF data has nonzero pivots because every pivot is normalized to one. -/
theorem hasNonzeroPivots [Lean.Grind.Field R]
    {M : Matrix R n m} {D : RowEchelonData R n m} (E : IsRREF M D) :
    E.toIsEchelonForm.HasNonzeroPivots := by
  intro i
  have hpivot :
      D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i] = 1 := by
    simpa [IsEchelonForm.pivotRow] using E.pivot_one i
  intro hzero
  exact (show (0 : R) ≠ 1 from Lean.Grind.Field.zero_ne_one) (hzero.symm.trans hpivot)

variable [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
variable {M : Matrix R n m} {D : RowEchelonData R n m}

/-- Find the pivot-row index for column `j`, if `j` is a pivot column. -/
private def pivotIndexAux (D : RowEchelonData R n m) (j : Fin m) (start fuel : Nat) :
    Option (Fin D.rank) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : start < D.rank then
        let i : Fin D.rank := ⟨start, h⟩
        if D.pivotCols.get i = j then
          some i
        else
          pivotIndexAux D j (start + 1) fuel
      else
        none

/-- Find the pivot-row index for column `j`, if `j` is a pivot column. -/
private def pivotIndex? (D : RowEchelonData R n m) (j : Fin m) : Option (Fin D.rank) :=
  pivotIndexAux D j 0 D.rank

private theorem pivotIndexAux_pivot (E : IsEchelonForm M D) (i : Fin D.rank) :
    ∀ start fuel,
      start ≤ i.val →
      i.val < start + fuel →
      pivotIndexAux D (D.pivotCols.get i) start fuel = some i := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro _ hlt
      omega
  | succ fuel ih =>
      intro hstart hlt
      unfold pivotIndexAux
      have hstartRank : start < D.rank := by omega
      simp [hstartRank]
      let s : Fin D.rank := ⟨start, hstartRank⟩
      by_cases hsi : s = i
      · have hcols : D.pivotCols.get s = D.pivotCols.get i := by rw [hsi]
        rw [if_pos hcols]
        change some s = some i
        exact congrArg some hsi
      · have hcols : D.pivotCols.get s ≠ D.pivotCols.get i := by
          intro hcols
          exact hsi (E.pivotCols_injective hcols)
        rw [if_neg hcols]
        apply ih (start := start + 1)
        · have hslt : start < i.val := by
            have hsne : start ≠ i.val := by
              intro hval
              exact hsi (Fin.ext hval)
            omega
          omega
        · omega

private theorem pivotIndex?_pivot (E : IsEchelonForm M D) (i : Fin D.rank) :
    pivotIndex? D (D.pivotCols.get i) = some i := by
  unfold pivotIndex?
  apply pivotIndexAux_pivot E i
  · omega
  · omega

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem pivotIndexAux_none_of_not_pivot {j : Fin m}
    (hnot : ∀ i : Fin D.rank, D.pivotCols.get i ≠ j) :
    ∀ start fuel, pivotIndexAux D j start fuel = none := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold pivotIndexAux
      by_cases hstart : start < D.rank
      · simp [hstart, hnot ⟨start, hstart⟩]
        exact ih (start + 1)
      · simp [hstart]

private theorem pivotIndex?_free_none (E : IsEchelonForm M D) (k : Fin (m - D.rank)) :
    pivotIndex? D (E.freeCols.get k) = none := by
  unfold pivotIndex?
  apply pivotIndexAux_none_of_not_pivot
  intro i
  exact E.pivotCols_disjoint_freeCols i k

/-- Nullspace basis vectors assembled as columns indexed by the free variables. -/
def nullspaceMatrix [Lean.Grind.Ring R] (E : IsRREF M D) :
    Matrix R m (m - D.rank) :=
  let freeCols := E.toIsEchelonForm.freeCols
  Matrix.ofFn fun j k =>
    if hFree : j = freeCols.get k then
      1
    else
      match pivotIndex? D j with
      | some i =>
          -D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm i)][freeCols.get k]
      | none => 0

private theorem nullspaceMatrix_free [Lean.Grind.Ring R] (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    E.nullspaceMatrix[E.toIsEchelonForm.freeCols.get k][k] = 1 := by
  unfold nullspaceMatrix Matrix.ofFn
  simp

private theorem nullspaceMatrix_free_ne [Lean.Grind.Ring R] (E : IsRREF M D)
    {k l : Fin (m - D.rank)} (hkl : k ≠ l) :
    E.nullspaceMatrix[E.toIsEchelonForm.freeCols.get l][k] = 0 := by
  unfold nullspaceMatrix Matrix.ofFn
  have hne : E.toIsEchelonForm.freeCols.get l ≠ E.toIsEchelonForm.freeCols.get k := by
    intro h
    exact hkl ((E.toIsEchelonForm.freeCols_injective h).symm)
  simp [hne, pivotIndex?_free_none E.toIsEchelonForm l]

private theorem nullspaceMatrix_pivot [Lean.Grind.Ring R] (E : IsRREF M D)
    (i : Fin D.rank) (k : Fin (m - D.rank)) :
    E.nullspaceMatrix[D.pivotCols.get i][k] =
      -(D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm i)][E.toIsEchelonForm.freeCols.get k]) := by
  unfold nullspaceMatrix Matrix.ofFn
  simp [E.toIsEchelonForm.pivotCols_disjoint_freeCols i k,
    pivotIndex?_pivot E.toIsEchelonForm i]

/-- The individual nullspace basis vectors. -/
def nullspace [Lean.Grind.Ring R] (E : IsRREF M D) :
    Vector (Vector R m) (m - D.rank) :=
  Vector.ofFn fun k => Matrix.col (E.nullspaceMatrix) k

private theorem nullspace_get [Lean.Grind.Ring R] (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    E.nullspace.get k = Matrix.col E.nullspaceMatrix k := by
  unfold nullspace
  rw [Vector.get_ofFn]

private theorem nullspace_get_free [Lean.Grind.Ring R] (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    (E.nullspace.get k)[E.toIsEchelonForm.freeCols.get k] = 1 := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_free E k

private theorem nullspace_get_free_ne [Lean.Grind.Ring R] (E : IsRREF M D)
    {k l : Fin (m - D.rank)} (hkl : k ≠ l) :
    (E.nullspace.get k)[E.toIsEchelonForm.freeCols.get l] = 0 := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_free_ne E hkl

private theorem nullspace_get_pivot [Lean.Grind.Ring R] (E : IsRREF M D)
    (i : Fin D.rank) (k : Fin (m - D.rank)) :
    (E.nullspace.get k)[D.pivotCols.get i] =
      -(D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm i)][E.toIsEchelonForm.freeCols.get k]) := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_pivot E i k

/-- Every basis vector returned by `nullspace` lies in the nullspace of `M`. -/
theorem nullspace_sound [Lean.Grind.Ring R] (E : IsRREF M D) (k : Fin (m - D.rank)) :
    M * E.nullspace.get k = 0 := by
  sorry

/-- Every nullspace vector is generated by the computed nullspace basis. -/
theorem nullspace_complete [Lean.Grind.Field R] (E : IsRREF M D) (v : Vector R m) :
    M * v = 0 → ∃ c : Vector R (m - D.rank), E.nullspaceMatrix * c = v := by
  sorry

end IsRREF

/-- Convenience wrapper: compute row-span coefficients using `rref` internally. -/
def spanCoeffs [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) :
    Option (Vector R n) :=
  let E := (rref_isRREF M).toIsEchelonForm
  E.spanCoeffs v

/-- Convenience wrapper: decide row-span membership using `rref` internally. -/
def spanContains [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) :
    Bool :=
  let E := (rref_isRREF M).toIsEchelonForm
  E.spanContains v

/-- The rank returned by `rref`. -/
def rref_rank [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) : Nat :=
  (rref M).rank

/-- Convenience wrapper: compute the nullspace basis using `rref` internally. -/
def nullspace [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) :
    Vector (Vector R m) (m - rref_rank M) :=
  let E := rref_isRREF M
  E.nullspace

end Matrix
end Hex
