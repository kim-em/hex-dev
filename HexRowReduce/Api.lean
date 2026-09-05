/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduce.Nullspace
public import HexMatrix.Submatrix
import HexMatrix.Pad
import all HexRowReduce.Nullspace

public section

/-!
Public `Matrix`-level wrappers backed by the executable `rowReduce`: the
row-span tests `spanCoeffs`/`spanContains`, the rank projection
`rowReduce_rank`, and the nullspace basis `nullspaceBasisMatrix`/`nullspace`.
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n m : Nat}

/-- Compute row-span coefficients using {name}`Hex.Matrix.rowReduce`
internally. -/
@[expose]
def spanCoeffs [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) :
    Option (Vector R n) :=
  let E := (rowReduce_isRowReduced M).toIsEchelonForm
  E.spanCoeffs v

/-- Soundness of {name}`Hex.Matrix.spanCoeffs`: returned coefficients reconstruct
the requested vector. -/
@[grind =>]
theorem spanCoeffs_sound [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (v : Vector R m) (c : Vector R n) :
    spanCoeffs M v = some c → vecMul c M = v := by
  intro h
  exact (rowReduce_isRowReduced M).toIsEchelonForm.spanCoeffs_sound v c h

/-- Decide row-span membership using {name}`Hex.Matrix.rowReduce` internally. -/
@[expose]
def spanContains [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) :
    Bool :=
  let E := (rowReduce_isRowReduced M).toIsEchelonForm
  E.spanContains v

/-- {name}`Hex.Matrix.spanContains` is the Boolean `isSome` view of
{name}`Hex.Matrix.spanCoeffs`. -/
@[simp, grind =] theorem spanContains_eq_isSome [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (v : Vector R m) :
    spanContains M v = (spanCoeffs M v).isSome := by
  rfl

/-- {name}`Hex.Matrix.spanContains` is exactly row-span membership. -/
@[grind =]
theorem spanContains_iff [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (v : Vector R m) :
    spanContains M v = true ↔ ∃ c : Vector R n, vecMul c M = v := by
  unfold spanContains
  simpa using (rowReduce_isRowReduced M).spanContains_iff v

/-- {name}`Hex.Matrix.spanCoeffs` returns `none` exactly when `v` is in no row combination of `M`,
so a `none` result certifies that `v` is not in the row span. -/
@[grind =]
theorem spanCoeffs_eq_none_iff [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (v : Vector R m) :
    spanCoeffs M v = none ↔ ¬ ∃ c : Vector R n, vecMul c M = v := by
  rw [← spanContains_iff, spanContains_eq_isSome]
  cases spanCoeffs M v <;> simp

/-- The rank returned by {name}`Hex.Matrix.rowReduce`. -/
@[expose]
def rowReduce_rank [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) : Nat :=
  (rowReduce M).rank

/-- A matrix with a right inverse has full row rank. -/
theorem rowReduce_rank_eq_n_of_rightInverse [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (Q : Matrix R m n)
    (hMQ : M * Q = Matrix.identity (R := R) n) :
    rowReduce_rank M = n := by
  let D := rowReduce M
  let E := rowReduce_isRowReduced M
  have hEQ : D.echelon * Q = D.transform := by
    calc
      D.echelon * Q = (D.transform * M) * Q := by rw [E.toIsEchelonForm.transform_mul]
      _ = D.transform * (M * Q) := Matrix.mul_assoc D.transform M Q
      _ = D.transform * Matrix.identity (R := R) n := by rw [hMQ]
      _ = D.transform := Matrix.mul_identity D.transform
  apply Nat.le_antisymm
  · exact E.toIsEchelonForm.rank_le_n
  · apply Nat.le_of_not_gt
    intro hlt
    let i : Fin n := ⟨D.rank, hlt⟩
    have hzeroE : Matrix.row D.echelon i = 0 :=
      E.toIsEchelonForm.zero_row i (Nat.le_refl D.rank)
    have hzeroT : Matrix.row D.transform i = 0 := by
      have hrow := congrArg (fun X : Matrix R n n => Matrix.row X i) hEQ
      rw [Matrix.row_mul_eq_zero D.echelon Q i hzeroE] at hrow
      exact hrow.symm
    rcases E.toIsEchelonForm.transform_right_inv with ⟨Tinv, hTinv⟩
    have hrowIdentity := congrArg (fun X : Matrix R n n => Matrix.row X i) hTinv
    rw [Matrix.row_mul_eq_zero D.transform Tinv i hzeroT] at hrowIdentity
    have hentry : (0 : Vector R n).get i =
        (Matrix.row (Matrix.identity (R := R) n) i).get i :=
      congrArg (fun v : Vector R n => v.get i) hrowIdentity
    have hz : (0 : Vector R n).get i = 0 := by
      simp [Vector.get]
    have hu : (Vector.unit R i).get i = 1 := by
      simp only [Vector.unit, Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]
      exact ite_eq_left (Fin.ext rfl)
    have huRow : (Matrix.row (Matrix.identity (R := R) n) i).get i = 1 := by
      rw [Matrix.row_identity]
      exact hu
    rw [hz, huRow] at hentry
    exact Lean.Grind.Field.zero_ne_one hentry

theorem takeRows_mul [Lean.Grind.Field R] [DecidableEq R]
    (A : Matrix R n m) (B : Matrix R m k) (r : Nat) (hr : r ≤ n) :
    Matrix.takeRows (A * B) r hr = Matrix.takeRows A r hr * B := by
  apply Matrix.ext_getElem
  intro i j
  rw [Matrix.getElem_takeRows, Matrix.getElem_mul, Matrix.getElem_mul]
  congr 1
  rw [Matrix.row_takeRows]

private theorem strictFin_eq_self {m : Nat} (f : Fin m → Fin m)
    (hstrict : ∀ i j, i < j → f i < f j) (i : Fin m) : f i = i := by
  have hlower : ∀ i : Fin m, i.val ≤ (f i).val := by
    intro i
    induction hi : i.val generalizing i with
    | zero => omega
    | succ k ih =>
        let prev : Fin m := ⟨k, by omega⟩
        have hprev := ih prev rfl
        have hs : (f prev).val < (f i).val := hstrict prev i (by
          show prev.val < i.val
          simp [prev, hi])
        have hprev' : k ≤ (f prev).val := by simpa [prev] using hprev
        have hs' : (f prev).val < (f i).val := hs
        omega
  have hupper : ∀ i : Fin m, (f i).val ≤ i.val := by
    intro i
    generalize ht : m - i.val = t
    induction t using Nat.strongRecOn generalizing i with
    | ind t ih =>
        by_cases hn : i.val + 1 < m
        · let next : Fin m := ⟨i.val + 1, hn⟩
          have hmeasure : m - (i.val + 1) < t := by omega
          have hnext := ih (m - next.val) (by simpa [next] using hmeasure) next rfl
          have hs : (f i).val < (f next).val := hstrict i next (by
            show i.val < next.val
            simp [next])
          have hnext' : (f next).val ≤ i.val + 1 := by simpa [next] using hnext
          omega
        · exact Nat.le_of_lt_succ (by omega)
  exact Fin.ext (Nat.le_antisymm (hupper i) (hlower i))

/-- If row reduction finds full column rank, the leading square block of
the reduced echelon form is the identity. -/
theorem rowReduce_takeRows_echelon_eq_identity [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (hm : m ≤ n) (hrank : rowReduce_rank M = m) :
    Matrix.takeRows (rowReduce M).echelon m hm = Matrix.identity (R := R) m := by
  let D := rowReduce M
  let E := rowReduce_isRowReduced M
  have hRank : D.rank = m := hrank
  let pivot : Fin m → Fin m := fun j =>
    D.pivotCols.get ⟨j.val, by rw [hRank]; exact j.isLt⟩
  have hpivot (j : Fin m) : pivot j = j := by
    apply strictFin_eq_self pivot
    intro i j hij
    exact E.toIsEchelonForm.pivotCols_sorted
      ⟨i.val, by rw [hRank]; exact i.isLt⟩
      ⟨j.val, by rw [hRank]; exact j.isLt⟩ hij
  apply Matrix.ext_getElem
  intro i j
  rw [Matrix.getElem_takeRows, Matrix.getElem_identity]
  let ii : Fin D.rank := ⟨i.val, by rw [hRank]; exact i.isLt⟩
  let jj : Fin D.rank := ⟨j.val, by rw [hRank]; exact j.isLt⟩
  have hpi : D.pivotCols.get ii = i := hpivot i
  have hpj : D.pivotCols.get jj = j := hpivot j
  by_cases hijv : i.val = j.val
  · have hij : i = j := Fin.ext hijv
    rw [ite_eq_left hij]
    have hone := E.pivot_one ii
    have hcol : D.pivotCols.get ii = j := hpi.trans hij
    change (rowReduce M).pivotCols.get ii = j at hcol
    let iN : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩
    have hrow : E.toIsEchelonForm.pivotRow ii = iN := Fin.ext rfl
    change (Matrix.row (rowReduce M).echelon
      (E.toIsEchelonForm.pivotRow ii)).get ((rowReduce M).pivotCols.get ii) = 1 at hone
    rw [hrow] at hone
    have hentry := congrArg
      (fun k : Fin m => (Matrix.row (rowReduce M).echelon iN).get k) hcol
    change (Matrix.row (rowReduce M).echelon iN).get j = 1
    exact hentry.symm.trans hone
  · have hij : i ≠ j := fun h => hijv (congrArg Fin.val h)
    rw [ite_eq_right hij]
    cases Nat.lt_or_gt_of_ne hijv with
    | inl hijv =>
        rw [← hpj]
        exact E.above_pivot_zero jj
          (⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩ : Fin n) hijv
    | inr hjiv =>
        rw [← hpj]
        exact E.toIsEchelonForm.below_pivot_zero jj
          (⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩ : Fin n) hjiv

/-- The computed rank is no larger than the middle dimension of any matrix
factorization. -/
theorem rowReduce_rank_le_of_eq_mul [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (C : Matrix R n k) (B : Matrix R k m)
    (hM : M = C * B) :
    rowReduce_rank M ≤ k := by
  let D := rowReduce M
  let E := rowReduce_isRowReduced M
  let d := D.rank
  let P : Matrix R d m := Matrix.takeRows D.echelon d E.toIsEchelonForm.rank_le_n
  let T : Matrix R d n := Matrix.takeRows D.transform d E.toIsEchelonForm.rank_le_n
  let Q : Matrix R m d := Matrix.ofFn fun i j =>
    if D.pivotCols.get j = i then (1 : R) else 0
  have hcolQ (j : Fin d) : Matrix.col Q j = Vector.unit R (D.pivotCols.get j) := by
    ext i hi
    let ii : Fin m := ⟨i, hi⟩
    show (Matrix.col Q j)[ii] = (Vector.unit R (D.pivotCols.get j))[ii]
    rw [Matrix.getElem_col, Matrix.getElem_ofFn, Vector.getElem_unit]
    have hone : (One.one : R) = 1 := rfl
    have hzero : (Zero.zero : R) = 0 := rfl
    rw [hone, hzero]
  have hPQ : P * Q = Matrix.identity (R := R) d := by
    apply Matrix.ext_getElem
    intro i j
    calc
      (P * Q)[i][j] = (P * Matrix.col Q j)[i] := by
        rw [Matrix.getElem_mul, Matrix.getElem_mulVec]
      _ = (Matrix.col P (D.pivotCols.get j))[i] := by
        rw [hcolQ, Matrix.mulVec_unit]
      _ = (Matrix.identity (R := R) d)[i][j] := by
        rw [Matrix.getElem_col, Matrix.getElem_identity]
        simp only [P, Matrix.getElem_takeRows]
        by_cases hij : i = j
        · subst j
          rw [ite_eq_left rfl]
          simpa [P, Matrix.IsEchelonForm.pivotRow] using E.pivot_one i
        · rw [ite_eq_right hij]
          cases Nat.lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with
          | inl hijv =>
              simpa [Matrix.IsEchelonForm.pivotRow] using
                E.above_pivot_zero j
                  (⟨i.val, Nat.lt_of_lt_of_le i.isLt E.toIsEchelonForm.rank_le_n⟩ : Fin n)
                  hijv
          | inr hjiv =>
              simpa [Matrix.IsEchelonForm.pivotRow] using
                E.toIsEchelonForm.below_pivot_zero j
                  (⟨i.val, Nat.lt_of_lt_of_le i.isLt E.toIsEchelonForm.rank_le_n⟩ : Fin n)
                  hjiv
  have hPM : P = T * M := by
    have htake := congrArg
      (fun X : Matrix R n m => Matrix.takeRows X d E.toIsEchelonForm.rank_le_n)
      E.toIsEchelonForm.transform_mul
    rw [takeRows_mul] at htake
    exact htake.symm
  have hfactor : P = (T * C) * B := by
    rw [hPM, hM, Matrix.mul_assoc]
  have hright : (T * C) * (B * Q) = Matrix.identity (R := R) d := by
    rw [← Matrix.mul_assoc, ← hfactor, hPQ]
  have hfull : rowReduce_rank (T * C) = d :=
    rowReduce_rank_eq_n_of_rightInverse (T * C) (B * Q) hright
  calc
    rowReduce_rank M = d := rfl
    _ = rowReduce_rank (T * C) := hfull.symm
    _ ≤ k := rowReduce_rank_le_m (T * C)

/-- A spanning family bounds the computed rank: if every row of `M` is a
combination of the rows of `B`, then `M` has rank at most the row count of
`B`. -/
theorem rowReduce_rank_le_of_rows_span [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (B : Matrix R k m)
    (hspan : ∀ i : Fin n, ∃ c : Vector R k, vecMul c B = row M i) :
    rowReduce_rank M ≤ k := by
  classical
  let C : Matrix R n k := Matrix.ofFn fun i j => (hspan i).choose[j]
  apply rowReduce_rank_le_of_eq_mul M C B
  apply Matrix.ext_getElem
  intro i j
  have hrow : Matrix.row C i = (hspan i).choose := by
    ext t ht
    let tt : Fin k := ⟨t, ht⟩
    change C[i][tt] = (hspan i).choose[tt]
    simp only [C, Matrix.getElem_ofFn]
  calc
    M[i][j] = (Matrix.row M i)[j] := by rw [Matrix.getElem_row]
    _ = (vecMul (hspan i).choose B)[j] := congrArg (fun v : Vector R m => v[j])
      (hspan i).choose_spec.symm
    _ = (vecMul (Matrix.row C i) B)[j] := by rw [hrow]
    _ = (C * B)[i][j] := by
      unfold vecMul
      rw [Matrix.getElem_mulVec, Matrix.row_transpose, Matrix.getElem_mul,
        Vector.dotProduct_comm]

/-- A right inverse supplies the matching lower rank bound. -/
theorem rowReduce_rank_ge_of_rightInverse [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (Q : Matrix R m n)
    (hMQ : M * Q = Matrix.identity (R := R) n) :
    n ≤ rowReduce_rank M := by
  rw [rowReduce_rank_eq_n_of_rightInverse M Q hMQ]
  exact Nat.le_refl n

private theorem pad_identity_mul [Lean.Grind.Field R] [DecidableEq R]
    (P : Matrix R k m) (_hk : k ≤ n) :
    Matrix.pad (Matrix.identity (R := R) k) n k * P = Matrix.pad P n m := by
  apply Matrix.ext_getElem
  intro i j
  by_cases hi : i.val < k
  · let ii : Fin k := ⟨i.val, hi⟩
    have hrow : Matrix.row (Matrix.pad (Matrix.identity (R := R) k) n k) i =
        Matrix.row (Matrix.identity (R := R) k) ii := by
      ext t ht
      let tt : Fin k := ⟨t, ht⟩
      change (Matrix.pad (Matrix.identity (R := R) k) n k)[i][tt] =
        (Matrix.identity (R := R) k)[ii][tt]
      rw [Matrix.getElem_pad,
        dite_eq_left (⟨hi, tt.isLt⟩ : i.val < k ∧ tt.val < k),
        Matrix.getElem_pair_eq_nested]
    calc
      (Matrix.pad (Matrix.identity (R := R) k) n k * P)[i][j] =
          ((Matrix.identity (R := R) k) * P)[ii][j] := by
        rw [Matrix.getElem_mul, Matrix.getElem_mul, hrow]
      _ = P[ii][j] := by rw [Matrix.identity_mul]
      _ = (Matrix.pad P n m)[i][j] := by
        rw [Matrix.getElem_pad, dite_eq_left (⟨hi, j.isLt⟩ : i.val < k ∧ j.val < m),
          Matrix.getElem_pair_eq_nested]
  · have hrow : Matrix.row (Matrix.pad (Matrix.identity (R := R) k) n k) i = 0 := by
      ext t ht
      let tt : Fin k := ⟨t, ht⟩
      change (Matrix.pad (Matrix.identity (R := R) k) n k)[i][tt] =
        (0 : Vector R k)[tt]
      rw [Matrix.getElem_pad, dite_eq_right (by simp [hi])]
      change (0 : R) = (0 : Vector R k)[tt.val]
      rw [Vector.getElem_zero]
    have hz := Matrix.row_mul_eq_zero
      (Matrix.pad (Matrix.identity (R := R) k) n k) P i hrow
    have hentry := congrArg (fun v : Vector R m => v[j]) hz
    change (Matrix.pad (Matrix.identity (R := R) k) n k * P)[i][j] =
      (0 : Vector R m)[j.val] at hentry
    rw [Vector.getElem_zero] at hentry
    rw [Matrix.getElem_pad, dite_eq_right (by simp [hi])]
    exact hentry

/-- The computed rank supplies an explicit factorization through that many
coordinates. -/
theorem rowReduce_rank_factorization [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) :
    ∃ C : Matrix R n (rowReduce_rank M), ∃ B : Matrix R (rowReduce_rank M) m,
      M = C * B := by
  let D := rowReduce M
  let E := rowReduce_isRowReduced M
  let d := D.rank
  let P : Matrix R d m := Matrix.takeRows D.echelon d E.toIsEchelonForm.rank_le_n
  rcases E.toIsEchelonForm.transform_inv with ⟨Tinv, hTinv⟩
  let J : Matrix R n d := Matrix.pad (Matrix.identity (R := R) d) n d
  refine ⟨Tinv * J, P, ?_⟩
  have hechelon : D.echelon = J * P := by
    rw [pad_identity_mul P E.toIsEchelonForm.rank_le_n]
    apply Matrix.ext_getElem
    intro i j
    rw [Matrix.getElem_pad]
    by_cases hi : i.val < d
    · rw [dite_eq_left (⟨hi, j.isLt⟩ : i.val < d ∧ j.val < m),
        Matrix.getElem_pair_eq_nested, Matrix.getElem_takeRows]
    · rw [dite_eq_right (by simp [hi])]
      have hrow := E.toIsEchelonForm.zero_row i (Nat.le_of_not_gt hi)
      have hentry := congrArg (fun v : Vector R m => v[j]) hrow
      change D.echelon[i][j] = (0 : Vector R m)[j.val] at hentry
      rw [Vector.getElem_zero] at hentry
      exact hentry
  calc
    M = (Matrix.identity (R := R) n) * M := (Matrix.identity_mul M).symm
    _ = (Tinv * D.transform) * M := by rw [hTinv]
    _ = Tinv * (D.transform * M) := Matrix.mul_assoc Tinv D.transform M
    _ = Tinv * D.echelon := by rw [E.toIsEchelonForm.transform_mul]
    _ = Tinv * (J * P) := by rw [hechelon]
    _ = (Tinv * J) * P := (Matrix.mul_assoc Tinv J P).symm

/-- Row reduction computes the same rank for a matrix and its transpose. -/
theorem rowReduce_rank_transpose [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) :
    rowReduce_rank (Matrix.transpose M) = rowReduce_rank M := by
  have rank_transpose_le (a b : Nat) (X : Matrix R a b) :
      rowReduce_rank (Matrix.transpose X) ≤ rowReduce_rank X := by
    rcases rowReduce_rank_factorization X with ⟨C, B, hX⟩
    apply rowReduce_rank_le_of_eq_mul
      (Matrix.transpose X) (Matrix.transpose B) (Matrix.transpose C)
    calc
      Matrix.transpose X = Matrix.transpose (C * B) := congrArg Matrix.transpose hX
      _ = Matrix.transpose B * Matrix.transpose C :=
        Matrix.transpose_mul_of_mul_comm C B
  apply Nat.le_antisymm
  · exact rank_transpose_le n m M
  · simpa using rank_transpose_le m n (Matrix.transpose M)

/-- The public nullspace basis assembled as a matrix of basis columns. -/
@[expose]
def nullspaceBasisMatrix [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) :
    Matrix R m (m - rowReduce_rank M) :=
  let E := rowReduce_isRowReduced M
  E.nullspaceMatrix

/-- Compute the nullspace basis using {name}`Hex.Matrix.rowReduce` internally. -/
@[expose]
def nullspace [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) :
    Vector (Vector R m) (m - rowReduce_rank M) :=
  let E := rowReduce_isRowReduced M
  E.nullspace

/-- The `k`-th column of {name}`Hex.Matrix.nullspaceBasisMatrix` is the `k`-th
vector in {name}`Hex.Matrix.nullspace`. -/
@[grind =>]
theorem nullspaceBasisMatrix_col [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (k : Fin (m - rowReduce_rank M)) :
    Matrix.col (nullspaceBasisMatrix M) k = (nullspace M).get k := by
  unfold nullspaceBasisMatrix nullspace
  exact ((rowReduce_isRowReduced M).nullspace_get k).symm

/-- Every vector returned by {name}`Hex.Matrix.nullspace` is annihilated by
`M`. -/
@[grind =>]
theorem nullspace_sound [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m)
    (k : Fin (m - rowReduce_rank M)) :
    M * (nullspace M).get k = 0 := by
  unfold nullspace rowReduce_rank
  exact (rowReduce_isRowReduced M).nullspace_sound k

/-- Every vector in the computed nullspace basis is nonzero. -/
theorem nullspace_ne_zero [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m)
    (k : Fin (m - rowReduce_rank M)) :
    (nullspace M).get k ≠ 0 := by
  unfold nullspace rowReduce_rank
  let E := rowReduce_isRowReduced M
  intro hz
  have hfree := E.nullspace_get_free k
  rw [hz] at hfree
  have hzero : (0 : Vector R m)[E.toIsEchelonForm.freeCols.get k] = 0 := by
    change (0 : Vector R m)[(E.toIsEchelonForm.freeCols.get k).val] = 0
    rw [Vector.getElem_zero]
  rw [hzero] at hfree
  exact Lean.Grind.Field.zero_ne_one hfree

/-- Every vector annihilated by `M` is generated by the public nullspace basis matrix. -/
@[grind =>]
theorem nullspace_complete [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m)
    (v : Vector R m) :
    M * v = 0 → ∃ c : Vector R (m - rowReduce_rank M), nullspaceBasisMatrix M * c = v := by
  intro hv
  unfold nullspaceBasisMatrix rowReduce_rank
  exact (rowReduce_isRowReduced M).nullspace_complete v hv



end Matrix
end Hex
