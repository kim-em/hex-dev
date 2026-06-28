module

public import HexMatrix.Determinant.Selection
import all HexMatrix.Determinant.Selection

public section

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-! ### Adjugate matrix and `M * adjugate M = det M • 1`

The local adjugate matrix is the transpose of the cofactor matrix. The
defining property is `(M * adjugate M)[i][j] = det M * δᵢⱼ`, which we
prove entrywise via Laplace expansion. The off-diagonal case uses the
"alien cofactor" identity: expanding row `i` against the cofactors of a
different row `j` collapses to the determinant of a matrix with two
equal rows. These are the Mathlib-free local analogues of Mathlib's
`Matrix.adjugate` and `Matrix.mul_adjugate` needed by the Desnanot-Jacobi
assembly. -/

/-- Replace row `dst` of `M` with the vector `v`. -/
@[expose]
def setRow {R : Type u} {n m : Nat}
    (M : Matrix R n m) (dst : Fin n) (v : Vector R m) : Matrix R n m :=
  M.set dst v

/-- Reading back the replaced row `dst` of `setRow M dst v` yields `v`. -/
@[grind =] theorem setRow_get_self {R : Type u} {n m : Nat}
    (M : Matrix R n m) (dst : Fin n) (v : Vector R m) :
    (setRow M dst v)[dst] = v := by
  simp [setRow]

/-- Replacing row `dst` leaves every other row unchanged. -/
theorem setRow_row_ne {R : Type u} {n m : Nat}
    (M : Matrix R n m) (dst r : Fin n) (v : Vector R m)
    (h : r ≠ dst) :
    (setRow M dst v)[r] = M[r] := by
  have hval : dst.val ≠ r.val := fun hval => h (Fin.ext hval.symm)
  exact Vector.getElem_set_ne (xs := M) (x := v) dst.isLt r.isLt hval

/-- Deleting the destination row of `setRow M dst v` gives the same minor
as deleting the destination row of `M`: the replaced row is removed
anyway, so the new entries are invisible. -/
theorem deleteRowCol_setRow_self {R : Type u} {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (dst col : Fin (n + 1))
    (v : Vector R (n + 1)) :
    deleteRowCol (setRow M dst v) dst col = deleteRowCol M dst col := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  change (deleteRowCol (setRow M dst v) dst col)[ii][jj] =
    (deleteRowCol M dst col)[ii][jj]
  rw [deleteRowCol_entry, deleteRowCol_entry]
  have hne : skipIndex dst ii ≠ dst := skipIndex_ne dst ii
  have hrow := setRow_row_ne M dst (skipIndex dst ii) v hne
  exact congrArg (fun row => row[skipIndex col jj]) hrow

/-- The cofactor expansion of `setRow M dst v` along the replaced row
`dst` uses the same minors as the cofactor expansion of `M` along that
row, because the deleted row never contributes to the minor. -/
theorem cofactor_setRow_self {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (dst col : Fin (n + 1))
    (v : Vector R (n + 1)) :
    cofactor (setRow M dst v) dst col = cofactor M dst col := by
  unfold cofactor
  rw [deleteRowCol_setRow_self M dst col v]

/-- Pair a row vector with a cofactor row of `M`. This is the scalar that
appears in Laplace expansion after replacing the expanded row. -/
@[expose]
def cofactorRowPairing {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row : Fin (n + 1)) (v : Vector R (n + 1)) :
    R :=
  (List.finRange (n + 1)).foldl
    (fun acc col => acc + v[col] * cofactor M row col) 0

/-- Replacing row `row` by `v` makes the determinant the pairing of `v`
against the original cofactor row. -/
theorem det_setRow_eq_cofactorRowPairing
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row : Fin (n + 1)) (v : Vector R (n + 1)) :
    det (setRow M row v) = cofactorRowPairing M row v := by
  rw [det_eq_foldl_laplace_row (setRow M row v) row]
  unfold cofactorRowPairing
  apply foldl_acc_congr
  intro acc col _hmem
  rw [show (setRow M row v)[row][col] = v[col] by
    rw [setRow_get_self]]
  rw [cofactor_setRow_self M row col v]

/-- Pairing the original row against its own cofactor row recovers `det M`. -/
theorem cofactorRowPairing_self
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row : Fin (n + 1)) :
    cofactorRowPairing M row M[row] = det M := by
  exact (det_eq_foldl_laplace_row M row).symm

/-- The "alien cofactor" identity: expanding row `i` of `M` against the
cofactors of a different row `j` produces zero. This is the
characteristic vanishing identity that makes the adjugate work. -/
theorem foldl_alien_cofactor_eq_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i j : Fin (n + 1)) (hij : i ≠ j) :
    (List.finRange (n + 1)).foldl
        (fun acc k => acc + M[i][k] * cofactor M j k) 0 = 0 := by
  let N : Matrix R (n + 1) (n + 1) := setRow M j M[i]
  have hNi : N[i] = M[i] := setRow_row_ne M j i M[i] hij
  have hNj : N[j] = M[i] := setRow_get_self M j M[i]
  have hrows : N[i] = N[j] := hNi.trans hNj.symm
  have hdetN : det N = 0 := det_eq_zero_of_row_eq N i j hij hrows
  have hLaplace := det_eq_foldl_laplace_row N j
  have hcof :
      (List.finRange (n + 1)).foldl
          (fun acc k => acc + N[j][k] * cofactor N j k) 0 =
        (List.finRange (n + 1)).foldl
          (fun acc k => acc + M[i][k] * cofactor M j k) 0 := by
    apply foldl_acc_congr
    intro acc k _hmem
    have hentry : N[j][k] = M[i][k] := congrArg (fun row => row[k]) hNj
    have hcofk : cofactor N j k = cofactor M j k :=
      cofactor_setRow_self M j k M[i]
    rw [hentry, hcofk]
  rw [hcof] at hLaplace
  exact hLaplace.symm.trans hdetN

/-- Pairing an unreplaced row of `M` against a different cofactor row is zero. -/
theorem cofactorRowPairing_alien_eq_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i j : Fin (n + 1)) (hij : i ≠ j) :
    cofactorRowPairing M j M[i] = 0 := by
  exact foldl_alien_cofactor_eq_zero M i j hij

/-- The local adjugate matrix: entry `(i, j)` is the cofactor at row `j`,
column `i` of `M`. This is the transpose of the cofactor matrix. -/
@[expose]
def adjugate {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) : Matrix R (n + 1) (n + 1) :=
  ofFn fun i j => cofactor M j i

/-- Entry `(i, j)` of the adjugate is the cofactor of `M` at row `j`, column `i`
(the transpose of the cofactor matrix). -/
@[grind =] theorem adjugate_get {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i j : Fin (n + 1)) :
    (adjugate M)[i][j] = cofactor M j i := by
  simp [adjugate, ofFn]

/-- Entrywise version of `M * adjugate M = det M • 1`. On the diagonal
this is Laplace expansion of `det M`; off the diagonal it is the alien
cofactor identity. -/
theorem mul_adjugate_apply {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i j : Fin (n + 1)) :
    (M * adjugate M)[i][j] =
      if i = j then det M else 0 := by
  have hmul : (M * adjugate M)[i][j] = Matrix.dot (row M i) (col (adjugate M) j) := by
    change (Matrix.mul M (adjugate M))[i][j] = _
    unfold Matrix.mul
    show (ofFn fun i j => Matrix.dot (row M i) (col (adjugate M) j))[i][j] = _
    simp [ofFn]
  have hentry :
      (M * adjugate M)[i][j] =
        (List.finRange (n + 1)).foldl
          (fun acc k => acc + M[i][k] * cofactor M j k) 0 := by
    rw [hmul]
    unfold Matrix.dot Hex.Vector.dotProduct
    apply foldl_acc_congr
    intro acc k _hmem
    congr 1
    have hrow : (row M i)[k] = M[i][k] := rfl
    have hcol : (col (adjugate M) j)[k] = (adjugate M)[k][j] := by
      simp [col]
    rw [hrow, hcol, adjugate_get]
  by_cases hij : i = j
  · subst hij
    rw [hentry, if_pos rfl]
    exact (det_eq_foldl_laplace_row M i).symm
  · rw [hentry, if_neg hij]
    exact foldl_alien_cofactor_eq_zero M i j hij

/-- Entrywise version of `adjugate M * M = det M • 1`.

This is the transpose-side companion to `mul_adjugate_apply`; it is useful
when cofactor identities are consumed columnwise rather than rowwise. -/
theorem adjugate_mul_apply {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i j : Fin (n + 1)) :
    (adjugate M * M)[i][j] =
      if i = j then det M else 0 := by
  have hentry :
      (adjugate M * M)[i][j] =
        (M.transpose * adjugate M.transpose)[j][i] := by
    have hleft :
        (adjugate M * M)[i][j] =
          (List.finRange (n + 1)).foldl
            (fun acc k => acc + cofactor M k i * M[k][j]) 0 := by
      change (Matrix.mul (adjugate M) M)[i][j] = _
      unfold Matrix.mul
      rw [getElem_ofFn]
      unfold Matrix.dot Hex.Vector.dotProduct
      apply foldl_acc_congr
      intro acc k _hmem
      have hrow : (row (adjugate M) i)[k] = (adjugate M)[i][k] := rfl
      have hcol : (col M j)[k] = M[k][j] := by
        simp [col]
      rw [hrow, hcol, adjugate_get]
    have hright :
        (M.transpose * adjugate M.transpose)[j][i] =
          (List.finRange (n + 1)).foldl
            (fun acc k => acc + M[k][j] * cofactor M k i) 0 := by
      change (Matrix.mul M.transpose (adjugate M.transpose))[j][i] = _
      unfold Matrix.mul
      rw [getElem_ofFn]
      unfold Matrix.dot Hex.Vector.dotProduct
      apply foldl_acc_congr
      intro acc k _hmem
      have hrow : (row M.transpose j)[k] = M[k][j] := by
        simp [row, transpose, col]
      have hcol : (col (adjugate M.transpose) i)[k] =
          cofactor M k i := by
        have hcol' : (col (adjugate M.transpose) i)[k] =
            (adjugate M.transpose)[k][i] := by
          simp [col]
        rw [hcol', adjugate_get, cofactor_transpose]
      rw [hrow, hcol]
    rw [hleft, hright]
    apply foldl_acc_congr
    intro acc k _hmem
    rw [Lean.Grind.CommSemiring.mul_comm]
  rw [hentry]
  rw [mul_adjugate_apply M.transpose j i]
  rw [det_transpose M]
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [if_neg hij]
    have hji : j ≠ i := fun h => hij h.symm
    rw [if_neg hji]

/-- Column-`0` view of `M * adjugate M`. -/
theorem mul_adjugate_apply_zero {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i : Fin (n + 1)) :
    (M * adjugate M)[i][(0 : Fin (n + 1))] =
      if i = 0 then det M else 0 :=
  mul_adjugate_apply M i 0

/-- Last-column view of `M * adjugate M`. -/
theorem mul_adjugate_apply_last {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i : Fin (n + 1)) :
    (M * adjugate M)[i][Fin.last n] =
      if i = Fin.last n then det M else 0 :=
  mul_adjugate_apply M i (Fin.last n)

/-- Cofactor-minor representation of an adjugate entry. -/
theorem adjugate_eq_cofactorSign_mul_deleteRowCol
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i j : Fin (n + 1)) :
    (adjugate M)[i][j] = cofactorSign j i * det (deleteRowCol M j i) := by
  rw [adjugate_get]
  rfl

/-- The `(0, 0)` adjugate entry equals the determinant of the minor
obtained by deleting row `0` and column `0`. -/
@[grind =] theorem adjugate_zero_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    (adjugate M)[(0 : Fin (n + 1))][(0 : Fin (n + 1))] =
      det (deleteRowCol M 0 0) := by
  rw [adjugate_get]
  exact cofactor_of_even M 0 0 (by simp)

/-- The `(Fin.last, Fin.last)` adjugate entry equals the determinant of
the leading prefix minor obtained by deleting the last row and column. -/
@[grind =] theorem adjugate_last_last
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    (adjugate M)[Fin.last n][Fin.last n] =
      det (leadingPrefix M n (Nat.le_succ n)) := by
  rw [adjugate_get]
  exact cofactor_last_last M

/-! ### Multiplicativity helpers

These private helpers prove determinant multiplicativity for Hex.det. -/

private theorem ofFn_toList_eq {α : Type v} {n : Nat}
    (f : Fin n → α) :
    (Vector.ofFn f).toList = (List.finRange n).map f := by
  rw [vector_toList_eq]
  apply List.map_congr_left
  intro i _
  exact vector_ofFn_getElem_fin f i

private theorem ofFn_mem_permutationVectors {n : Nat}
    (cols : Fin n → Fin n) (hcols : Function.Injective cols) :
    Vector.ofFn cols ∈ permutationVectors n := by
  apply permutationVectors_complete
  rw [ofFn_toList_eq]
  apply list_nodup_map_on (List.nodup_finRange n)
  intro a _ha b _hb hab
  exact hcols hab

private theorem columnTupleMatrix_eq_ofFn_ofFn
    {R : Type u} {n : Nat} (M : Matrix R n n) (cols : Fin n → Fin n) :
    columnTupleMatrix M cols =
      (ofFn fun r c => M[r][(Vector.ofFn cols)[c]] : Matrix R n n) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  show (columnTupleMatrix M cols)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
    (ofFn (fun r c => M[r][(Vector.ofFn cols)[c]]) : Matrix R n n)[
      (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnTupleMatrix_entry]
  unfold ofFn
  rw [vector_ofFn_getElem_fin, vector_ofFn_getElem_fin]
  exact congrArg (fun col : Fin n => M[(⟨r, hr⟩ : Fin n)][col])
    (vector_ofFn_getElem_fin cols (⟨c, hc⟩ : Fin n)).symm

private theorem det_columnTupleMatrix_of_injective
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (cols : Fin n → Fin n)
    (hcols : Function.Injective cols) :
    det (columnTupleMatrix M cols) =
      detSign (R := R) (Vector.ofFn cols) * det M := by
  have hmem : Vector.ofFn cols ∈ permutationVectors n :=
    ofFn_mem_permutationVectors cols hcols
  rw [columnTupleMatrix_eq_ofFn_ofFn M cols]
  exact det_colPermute_vector M (Vector.ofFn cols) hmem

private theorem det_columnTupleMatrix_eq
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (cols : Fin n → Fin n) :
    det (columnTupleMatrix M cols) =
      det M * det (columnTupleMatrix (1 : Matrix R n n) cols) := by
  by_cases hinj : Function.Injective cols
  · rw [det_columnTupleMatrix_of_injective M cols hinj,
        det_columnTupleMatrix_of_injective (1 : Matrix R n n) cols hinj]
    rw [det_one]
    grind
  · rw [det_columnTupleMatrix_eq_zero_of_not_injective M cols hinj,
        det_columnTupleMatrix_eq_zero_of_not_injective (1 : Matrix R n n) cols hinj]
    grind

private theorem mul_eq_columnSumMatrix_transpose
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M N : Matrix R n n) :
    M * N = columnSumMatrix M N.transpose := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  let rr : Fin n := ⟨r, hr⟩
  let cc : Fin n := ⟨c, hc⟩
  show (M * N)[rr][cc] = (columnSumMatrix M N.transpose)[rr][cc]
  rw [columnSumMatrix_entry]
  change (Matrix.mul M N)[rr][cc] = _
  unfold Matrix.mul ofFn
  rw [vector_ofFn_getElem_fin, vector_ofFn_getElem_fin]
  unfold Matrix.dot Hex.Vector.dotProduct
  apply foldl_det_sum_congr
  intro k _
  have hrow : (row M rr)[k] = M[rr][k] := by simp [row]
  have hcol : (col N cc)[k] = N[k][cc] := by
    show (Vector.ofFn (fun i : Fin n => N[i][cc]))[k] = N[k][cc]
    exact vector_ofFn_getElem_fin _ k
  have htrn : N.transpose[cc][k] = N[k][cc] := by
    show (Vector.ofFn (fun j : Fin n => col N j))[cc][k] = N[k][cc]
    rw [vector_ofFn_getElem_fin]
    exact hcol
  rw [hrow, hcol, htrn]
  exact Lean.Grind.CommSemiring.mul_comm _ _

private theorem eq_columnSumMatrix_one_transpose
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (N : Matrix R n n) :
    N = columnSumMatrix (1 : Matrix R n n) N.transpose := by
  rw [← mul_eq_columnSumMatrix_transpose (1 : Matrix R n n) N]
  exact (one_mul N).symm

/-- Determinant of a product of square matrices.

This is the Mathlib-free Cauchy-Binet specialization already used by the
Desnanot-Jacobi auxiliary proof. -/
theorem det_mul
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M N : Matrix R n n) :
    det (M * N) = det M * det N := by
  rw [mul_eq_columnSumMatrix_transpose M N]
  rw [det_columnSumMatrix_eq_sum_columnTuples M N.transpose]
  have hbody_eq :
      (columnTupleVectors n n).foldl
          (fun acc cols => acc +
            columnTupleCoeff N.transpose cols *
              det (columnTupleMatrix M (columnTupleVectorFn cols))) 0 =
        (columnTupleVectors n n).foldl
          (fun acc cols => acc + det M *
            (columnTupleCoeff N.transpose cols *
              det (columnTupleMatrix (1 : Matrix R n n)
                (columnTupleVectorFn cols)))) 0 := by
    apply foldl_det_sum_congr
    intro cols _
    rw [det_columnTupleMatrix_eq M (columnTupleVectorFn cols)]
    exact Lean.Grind.CommSemiring.mul_left_comm _ _ _
  rw [hbody_eq]
  rw [foldl_det_sum_mul_left_zero
        (columnTupleVectors n n)
        (det M)
        (fun cols => columnTupleCoeff N.transpose cols *
            det (columnTupleMatrix (1 : Matrix R n n)
              (columnTupleVectorFn cols)))]
  rw [← det_columnSumMatrix_eq_sum_columnTuples
        (1 : Matrix R n n) N.transpose]
  rw [← eq_columnSumMatrix_one_transpose N]

/-! ### Plucker minor helpers

Encoding for the universal 3-term Plucker identity substrate. -/

/-- Embed `Fin n` into `Fin (n + 2)` while skipping two deleted indices
`p < q`. This indexes minors with two removed rows.

The ordering proof `_hpq` is a phantom argument: it documents and pins the
`p < q` precondition at call sites but is not consumed by the definition.
This intentionally triggers the `unusedArguments` linter; the binder is kept
deliberately (no `@[nolint]` exists in the Mathlib-free layer). -/
@[expose]
def skipIndex2 {n : Nat} (p q : Fin (n + 2)) (_hpq : p.val < q.val)
    (i : Fin n) : Fin (n + 2) :=
  if hi1 : i.val < p.val then
    ⟨i.val, by have hp := p.isLt; omega⟩
  else if hi2 : i.val + 1 < q.val then
    ⟨i.val + 1, by have hq := q.isLt; omega⟩
  else
    ⟨i.val + 2, by have hi := i.isLt; omega⟩

/-- Below the first deleted index `p`, `skipIndex2` is the identity: its value
at `i` is `i`. -/
@[simp, grind =] theorem skipIndex2_val_of_lt_p {n : Nat} (p q : Fin (n + 2))
    (hpq : p.val < q.val) (i : Fin n) (h : i.val < p.val) :
    (skipIndex2 p q hpq i).val = i.val := by
  simp [skipIndex2, h]

/-- Between the two deleted indices `p` and `q`, `skipIndex2` shifts up by one:
its value at `i` is `i + 1`. -/
@[simp, grind =] theorem skipIndex2_val_of_between {n : Nat} (p q : Fin (n + 2))
    (hpq : p.val < q.val) (i : Fin n) (h1 : ¬ i.val < p.val)
    (h2 : i.val + 1 < q.val) :
    (skipIndex2 p q hpq i).val = i.val + 1 := by
  simp [skipIndex2, h1, h2]

/-- At or beyond the second deleted index `q`, `skipIndex2` shifts up by two:
its value at `i` is `i + 2`. -/
@[simp, grind =] theorem skipIndex2_val_of_ge_q {n : Nat} (p q : Fin (n + 2))
    (hpq : p.val < q.val) (i : Fin n) (h1 : ¬ i.val < p.val)
    (h2 : ¬ i.val + 1 < q.val) :
    (skipIndex2 p q hpq i).val = i.val + 2 := by
  simp [skipIndex2, h1, h2]

/-- `skipIndex2 p q hpq` never lands on the first skipped index `p`. -/
theorem skipIndex2_ne_p {n : Nat} (p q : Fin (n + 2)) (hpq : p.val < q.val)
    (i : Fin n) : skipIndex2 p q hpq i ≠ p := by
  intro hsame
  have hval : (skipIndex2 p q hpq i).val = p.val := congrArg Fin.val hsame
  by_cases h1 : i.val < p.val
  · rw [skipIndex2_val_of_lt_p p q hpq i h1] at hval; omega
  · by_cases h2 : i.val + 1 < q.val
    · rw [skipIndex2_val_of_between p q hpq i h1 h2] at hval; omega
    · rw [skipIndex2_val_of_ge_q p q hpq i h1 h2] at hval; omega

/-- `skipIndex2 p q hpq` never lands on the second skipped index `q`. -/
theorem skipIndex2_ne_q {n : Nat} (p q : Fin (n + 2)) (hpq : p.val < q.val)
    (i : Fin n) : skipIndex2 p q hpq i ≠ q := by
  intro hsame
  have hval : (skipIndex2 p q hpq i).val = q.val := congrArg Fin.val hsame
  by_cases h1 : i.val < p.val
  · rw [skipIndex2_val_of_lt_p p q hpq i h1] at hval; omega
  · by_cases h2 : i.val + 1 < q.val
    · rw [skipIndex2_val_of_between p q hpq i h1 h2] at hval; omega
    · rw [skipIndex2_val_of_ge_q p q hpq i h1 h2] at hval; omega

/-- The `(n + 1) × (n + 1)` matrix obtained from `[B | v]` by deleting
row `p`. Columns `0..n-1` carry the corresponding columns of `B`
(restricted to rows other than `p`); the last column carries `v`
(restricted to rows other than `p`). -/
@[expose]
def mMatrix {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (v : Vector R (n + 2)) (p : Fin (n + 2)) :
    Matrix R (n + 1) (n + 1) :=
  ofFn fun i j =>
    if hj : j.val < n then
      B[skipIndex p i][(⟨j.val, hj⟩ : Fin n)]
    else
      v[skipIndex p i]

/-- In a non-last column, `mMatrix` reads the corresponding entry of `B`
through the row-deletion map. -/
theorem mMatrix_entry_lt {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (v : Vector R (n + 2)) (p : Fin (n + 2))
    (i : Fin (n + 1)) (j : Fin (n + 1)) (h : j.val < n) :
    (mMatrix B v p)[i][j] = B[skipIndex p i][(⟨j.val, h⟩ : Fin n)] := by
  unfold mMatrix
  rw [getElem_ofFn]
  exact dif_pos h

/-- The last column of `mMatrix B v p` is the vector `v` with row `p`
deleted. -/
theorem mMatrix_entry_last {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (v : Vector R (n + 2)) (p : Fin (n + 2))
    (i : Fin (n + 1)) :
    (mMatrix B v p)[i][Fin.last n] = v[skipIndex p i] := by
  have h : ¬ (Fin.last n : Fin (n + 1)).val < n := by
    simp [Fin.last]
  unfold mMatrix
  rw [getElem_ofFn]
  exact dif_neg h

/-- The determinant of `mMatrix B v p`: the `(n + 1)`-maximal minor of
`[B | v]` with row `p` deleted. -/
@[expose]
def mDet {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (v : Vector R (n + 2)) (p : Fin (n + 2)) : R :=
  det (mMatrix B v p)

/-- The `n × n` matrix obtained from `B` by deleting rows `p` and `q`
(in increasing-row order, with `p.val < q.val`). -/
@[expose]
def nMatrix {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (p q : Fin (n + 2)) (hpq : p.val < q.val) :
    Matrix R n n :=
  ofFn fun i j => B[skipIndex2 p q hpq i][j]

/-- Entry `(i, j)` of the two-row-deleted minor `nMatrix B p q hpq` is the source
entry `B[skipIndex2 p q hpq i][j]`. -/
@[grind =] theorem nMatrix_entry {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (p q : Fin (n + 2)) (hpq : p.val < q.val)
    (i : Fin n) (j : Fin n) :
    (nMatrix B p q hpq)[i][j] = B[skipIndex2 p q hpq i][j] := by
  simp [nMatrix, ofFn]

/-- The determinant of `nMatrix B p q hpq`: the `n × n` minor of `B`
with rows `p, q` deleted. -/
@[expose]
def nDet {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (p q : Fin (n + 2)) (hpq : p.val < q.val) : R :=
  det (nMatrix B p q hpq)

/-! ### Row-move infrastructure for ordered four-row transports

These helpers transport the determinant of a matrix whose rows are an
ordered `nMatrix` row sequence with one row displaced downward. Each
"row-move" is realised as a chain of adjacent `rowSwap`s; the determinant
picks up `(-1) ^ k` for a `k`-step move. The four row-content lemmas
identify the rows of the moved matrix so consumers can pair them with
`nMatrix_entry` / `skipIndex2` value lemmas. -/

/-- Move the row at position `src + k` of `M` to position `src` by `k`
adjacent row swaps. The rows previously at positions `src, …, src + k - 1`
shift right by one to positions `src + 1, …, src + k`. Rows outside the
interval `[src, src + k]` are unchanged. -/
private def rowMoveUp {R : Type u} {n m : Nat} (M : Matrix R n m) (src : Nat) :
    (k : Nat) → src + k < n → Matrix R n m
  | 0, _ => M
  | k + 1, h =>
    rowMoveUp
      (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) src k (by omega)

@[simp, grind =] private theorem rowMoveUp_zero {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src : Nat) (h : src + 0 < n) :
    rowMoveUp M src 0 h = M := rfl

private theorem rowMoveUp_succ {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src k : Nat) (h : src + (k + 1) < n) :
    rowMoveUp M src (k + 1) h =
      rowMoveUp (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) src k
        (by omega) := rfl

/-- Determinant contribution of `rowMoveUp`: each of the `k` adjacent
swaps negates the determinant. -/
private theorem det_rowMoveUp {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src k : Nat) (h : src + k < n) :
    det (rowMoveUp M src k h) = (-1 : R) ^ k * det M := by
  induction k generalizing M with
  | zero => simp; grind
  | succ k ih =>
      rw [rowMoveUp_succ]
      have hne : (⟨src + k, by omega⟩ : Fin n) ≠ ⟨src + k + 1, h⟩ := by
        intro heq
        have hv : (⟨src + k, by omega⟩ : Fin n).val =
            (⟨src + k + 1, h⟩ : Fin n).val := congrArg Fin.val heq
        simp at hv
      rw [ih]
      rw [det_rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩ hne]
      rw [Lean.Grind.Semiring.pow_succ]
      grind

/-- Rows of `M` strictly below the move interval are unchanged by
`rowMoveUp`. -/
private theorem rowMoveUp_row_of_lt {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src k : Nat) (h : src + k < n) (i : Fin n)
    (hi : i.val < src) :
    (rowMoveUp M src k h)[i] = M[i] := by
  induction k generalizing M with
  | zero => rfl
  | succ k ih =>
      rw [rowMoveUp_succ]
      rw [ih (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) (by omega)]
      apply Vector.ext
      intro j hj
      let jj : Fin m := ⟨j, hj⟩
      show (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩)[i][jj] = M[i][jj]
      rw [rowSwap_get]
      have h_ne_j : i ≠ ⟨src + k + 1, h⟩ := by
        intro heq; have := congrArg Fin.val heq; simp at this; omega
      have h_ne_i : i ≠ ⟨src + k, by omega⟩ := by
        intro heq; have := congrArg Fin.val heq; simp at this; omega
      rw [if_neg h_ne_j, if_neg h_ne_i]

/-- Rows of `M` strictly above the move interval are unchanged by
`rowMoveUp`. -/
private theorem rowMoveUp_row_of_gt {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src k : Nat) (h : src + k < n) (i : Fin n)
    (hi : src + k < i.val) :
    (rowMoveUp M src k h)[i] = M[i] := by
  induction k generalizing M with
  | zero => rfl
  | succ k ih =>
      rw [rowMoveUp_succ]
      rw [ih (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) (by omega)
        (by omega)]
      apply Vector.ext
      intro j hj
      let jj : Fin m := ⟨j, hj⟩
      show (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩)[i][jj] = M[i][jj]
      rw [rowSwap_get]
      have h_ne_j : i ≠ ⟨src + k + 1, h⟩ := by
        intro heq; have := congrArg Fin.val heq; simp at this; omega
      have h_ne_i : i ≠ ⟨src + k, by omega⟩ := by
        intro heq; have := congrArg Fin.val heq; simp at this; omega
      rw [if_neg h_ne_j, if_neg h_ne_i]

/-- The bottom of the move interval (`i.val = src`) receives the row
originally at the top of the interval (`src + k`). -/
private theorem rowMoveUp_row_eq_src {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src k : Nat) (h : src + k < n) (i : Fin n)
    (hi : i.val = src) :
    (rowMoveUp M src k h)[i] = M[(⟨src + k, h⟩ : Fin n)] := by
  induction k generalizing M with
  | zero =>
      have hii : i = (⟨src + 0, h⟩ : Fin n) := Fin.ext (by simp [hi])
      rw [hii]; rfl
  | succ k ih =>
      rw [rowMoveUp_succ]
      rw [ih (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) (by omega)]
      apply Vector.ext
      intro j hj
      let jj : Fin m := ⟨j, hj⟩
      show (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩)[
          (⟨src + k, by omega⟩ : Fin n)][jj]
          = M[(⟨src + (k + 1), h⟩ : Fin n)][jj]
      rw [rowSwap_get]
      have h_ne_j : (⟨src + k, by omega⟩ : Fin n) ≠ ⟨src + k + 1, h⟩ := by
        intro heq; have := congrArg Fin.val heq; simp at this
      rw [if_neg h_ne_j, if_pos rfl]
      have hii : (⟨src + k + 1, h⟩ : Fin n) = ⟨src + (k + 1), h⟩ := by
        apply Fin.ext; simp; omega
      rw [hii]

/-- Strictly inside the move interval (`src < i.val ≤ src + k`), the row
at position `i` of `rowMoveUp` is the row originally at position
`i.val - 1`: each row shifted right by one to make room for the inserted
row at `src`. -/
private theorem rowMoveUp_row_between {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src k : Nat) (h : src + k < n) (i : Fin n)
    (hi_lt : src < i.val) (hi_le : i.val ≤ src + k) :
    (rowMoveUp M src k h)[i] =
      M[(⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n)] := by
  induction k generalizing M with
  | zero =>
      -- src < i.val ≤ src + 0 = src is empty
      omega
  | succ k ih =>
      rw [rowMoveUp_succ]
      by_cases h_lt : i.val ≤ src + k
      · -- Inductive case: still in the move interval after one swap
        rw [ih (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) (by omega)
          h_lt]
        apply Vector.ext
        intro j hj
        let jj : Fin m := ⟨j, hj⟩
        show (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩)[
            (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n)][jj] =
          M[(⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n)][jj]
        rw [rowSwap_get]
        have h_ne_j :
            (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n)
              ≠ ⟨src + k + 1, h⟩ := by
          intro heq; have := congrArg Fin.val heq; simp at this; omega
        have h_ne_i :
            (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n)
              ≠ ⟨src + k, by omega⟩ := by
          intro heq; have := congrArg Fin.val heq; simp at this; omega
        rw [if_neg h_ne_j, if_neg h_ne_i]
      · -- Boundary case: i.val = src + k + 1
        have hi_eq : i.val = src + k + 1 := by omega
        have h_gt : src + k < i.val := by omega
        rw [rowMoveUp_row_of_gt
          (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩) src k
          (by omega) i h_gt]
        apply Vector.ext
        intro j hj
        let jj : Fin m := ⟨j, hj⟩
        show (rowSwap M ⟨src + k, by omega⟩ ⟨src + k + 1, h⟩)[i][jj] =
          M[(⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n)][jj]
        rw [rowSwap_get]
        have h_eq_j : i = (⟨src + k + 1, h⟩ : Fin n) := by
          apply Fin.ext; simp [hi_eq]
        rw [if_pos h_eq_j]
        have hii : (⟨src + k, by omega⟩ : Fin n) =
            ⟨i.val - 1, by have := i.isLt; omega⟩ := by
          apply Fin.ext; simp; omega
        rw [hii]

/-! ### One-row `setRow` transports to ordered `nDet` minors

For `a < b < t` in `Fin (n + 2)`, the private helpers
`rowMoveUp_setRow_nMatrix_replace_first` and
`_replace_second_eq_nMatrix` identify the result of replacing the
`(t.val - 2)`-th row of `nMatrix B a b hab` with `B[a]` (respectively
`B[b]`) as a `rowMoveUp` of the ordered minor `nMatrix B b t` (resp.
`nMatrix B a t`). The four ordered four-row transports
`det_setRow_nMatrix_r{2,3}_r{0,1}_eq_pow_mul_nDet_*` combine these row
equalities with `det_rowMoveUp` to give the signed `nDet` lemmas
required by the ordered four-row Plucker assembly. -/

/-- For `a < b < t`, replacing row `s` (with `s.val = t.val - 2`) of
`nMatrix B a b hab` by `B[a]` and then sliding that row up to position
`a.val` by `t.val - a.val - 2` adjacent swaps reproduces
`nMatrix B b t hbt`. -/
private theorem rowMoveUp_setRow_nMatrix_replace_first
    {R : Type u} {n : Nat} (B : Matrix R (n + 2) n)
    (a b t : Fin (n + 2)) (hab : a.val < b.val) (hbt : b.val < t.val)
    (s : Fin n) (hs : s.val = t.val - 2)
    (hsk : a.val + (t.val - a.val - 2) < n) :
    rowMoveUp (setRow (nMatrix B a b hab) s B[a]) a.val
        (t.val - a.val - 2) hsk =
      nMatrix B b t hbt := by
  apply Vector.ext
  intro i hi
  let ii : Fin n := ⟨i, hi⟩
  show (rowMoveUp (setRow (nMatrix B a b hab) s B[a]) a.val
        (t.val - a.val - 2) hsk)[ii] = (nMatrix B b t hbt)[ii]
  by_cases h_below : ii.val < a.val
  · -- Below the move interval: both rowMoveUp and setRow leave the row alone.
    have hii_ne_s : ii ≠ s := by
      intro he
      have hv : ii.val = s.val := congrArg Fin.val he
      rw [hs] at hv
      have : a.val < t.val := Nat.lt_trans hab hbt
      omega
    rw [rowMoveUp_row_of_lt (setRow (nMatrix B a b hab) s B[a]) a.val
          (t.val - a.val - 2) hsk ii h_below,
        setRow_row_ne (nMatrix B a b hab) s ii B[a] hii_ne_s]
    apply Vector.ext
    intro j hj
    let jj : Fin n := ⟨j, hj⟩
    show (nMatrix B a b hab)[ii][jj] = (nMatrix B b t hbt)[ii][jj]
    rw [nMatrix_entry, nMatrix_entry]
    have hii_lt_b : ii.val < b.val := Nat.lt_trans h_below hab
    have hidx : skipIndex2 a b hab ii = skipIndex2 b t hbt ii := by
      apply Fin.ext
      rw [skipIndex2_val_of_lt_p a b hab ii h_below,
          skipIndex2_val_of_lt_p b t hbt ii hii_lt_b]
    exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx
  · by_cases h_eq : ii.val = a.val
    · -- At the source of the move: the inserted row B[a] surfaces here.
      have h_row_eq :
          (rowMoveUp (setRow (nMatrix B a b hab) s B[a]) a.val
              (t.val - a.val - 2) hsk)[ii] = B[a] := by
        rw [rowMoveUp_row_eq_src (setRow (nMatrix B a b hab) s B[a]) a.val
              (t.val - a.val - 2) hsk ii h_eq]
        have hidx_eq :
            (⟨a.val + (t.val - a.val - 2), hsk⟩ : Fin n) = s := by
          apply Fin.ext
          show a.val + (t.val - a.val - 2) = s.val
          rw [hs]; omega
        calc (setRow (nMatrix B a b hab) s B[a])[
              (⟨a.val + (t.val - a.val - 2), hsk⟩ : Fin n)]
            = (setRow (nMatrix B a b hab) s B[a])[s] :=
              congrArg
                (fun (i : Fin n) =>
                  (setRow (nMatrix B a b hab) s B[a])[i]) hidx_eq
          _ = B[a] := setRow_get_self _ _ _
      rw [h_row_eq]
      apply Vector.ext
      intro j hj
      let jj : Fin n := ⟨j, hj⟩
      show B[a][jj] = (nMatrix B b t hbt)[ii][jj]
      rw [nMatrix_entry]
      have hii_lt_b : ii.val < b.val := by rw [h_eq]; exact hab
      have hidx : skipIndex2 b t hbt ii = a := by
        apply Fin.ext
        rw [skipIndex2_val_of_lt_p b t hbt ii hii_lt_b]
        exact h_eq
      exact (congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx).symm
    · by_cases h_above : t.val - 2 < ii.val
      · -- Above the move interval: both rowMoveUp and setRow leave the row alone.
        have h_above' : a.val + (t.val - a.val - 2) < ii.val := by
          have : a.val + (t.val - a.val - 2) = t.val - 2 := by omega
          rw [this]; exact h_above
        rw [rowMoveUp_row_of_gt (setRow (nMatrix B a b hab) s B[a]) a.val
              (t.val - a.val - 2) hsk ii h_above']
        have hii_ne_s : ii ≠ s := by
          intro he
          have hv : ii.val = s.val := congrArg Fin.val he
          rw [hs] at hv; omega
        rw [setRow_row_ne (nMatrix B a b hab) s ii B[a] hii_ne_s]
        apply Vector.ext
        intro j hj
        let jj : Fin n := ⟨j, hj⟩
        show (nMatrix B a b hab)[ii][jj] = (nMatrix B b t hbt)[ii][jj]
        rw [nMatrix_entry, nMatrix_entry]
        have h_not_lt_a : ¬ ii.val < a.val := h_below
        have h_not_between_lhs : ¬ ii.val + 1 < b.val := by omega
        have h_not_lt_b_rhs : ¬ ii.val < b.val := by omega
        have h_not_between_rhs : ¬ ii.val + 1 < t.val := by omega
        have hidx : skipIndex2 a b hab ii = skipIndex2 b t hbt ii := by
          apply Fin.ext
          rw [skipIndex2_val_of_ge_q a b hab ii h_not_lt_a h_not_between_lhs,
              skipIndex2_val_of_ge_q b t hbt ii h_not_lt_b_rhs h_not_between_rhs]
        exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx
      · -- Inside the move interval (strictly): rows shift right by one.
        have h_lt_src : a.val < ii.val := by
          have h1 : ¬ ii.val < a.val := h_below
          have h2 : ii.val ≠ a.val := h_eq
          omega
        have h_le_top : ii.val ≤ a.val + (t.val - a.val - 2) := by
          have : a.val + (t.val - a.val - 2) = t.val - 2 := by omega
          rw [this]; omega
        rw [rowMoveUp_row_between (setRow (nMatrix B a b hab) s B[a]) a.val
              (t.val - a.val - 2) hsk ii h_lt_src h_le_top]
        let j_minus : Fin n := ⟨ii.val - 1, by have := ii.isLt; omega⟩
        have hj_ne_s : j_minus ≠ s := by
          intro he
          have hv : j_minus.val = s.val := congrArg Fin.val he
          rw [hs] at hv
          have : ii.val - 1 = t.val - 2 := hv
          omega
        rw [setRow_row_ne (nMatrix B a b hab) s j_minus B[a] hj_ne_s]
        apply Vector.ext
        intro j hj
        let jj : Fin n := ⟨j, hj⟩
        show (nMatrix B a b hab)[j_minus][jj] = (nMatrix B b t hbt)[ii][jj]
        rw [nMatrix_entry, nMatrix_entry]
        have h_not_lt_a : ¬ j_minus.val < a.val := by
          show ¬ ii.val - 1 < a.val; omega
        by_cases h_below_b : ii.val < b.val
        · have h_between_lhs : j_minus.val + 1 < b.val := by
            show ii.val - 1 + 1 < b.val; omega
          have h_lt_b_rhs : ii.val < b.val := h_below_b
          have hidx : skipIndex2 a b hab j_minus = skipIndex2 b t hbt ii := by
            apply Fin.ext
            rw [skipIndex2_val_of_between a b hab j_minus h_not_lt_a
                  h_between_lhs,
                skipIndex2_val_of_lt_p b t hbt ii h_lt_b_rhs]
            show ii.val - 1 + 1 = ii.val
            omega
          exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx
        · have h_not_between_lhs : ¬ j_minus.val + 1 < b.val := by
            show ¬ ii.val - 1 + 1 < b.val; omega
          have h_not_lt_b_rhs : ¬ ii.val < b.val := h_below_b
          have h_between_rhs : ii.val + 1 < t.val := by omega
          have hidx : skipIndex2 a b hab j_minus = skipIndex2 b t hbt ii := by
            apply Fin.ext
            rw [skipIndex2_val_of_ge_q a b hab j_minus h_not_lt_a
                  h_not_between_lhs,
                skipIndex2_val_of_between b t hbt ii h_not_lt_b_rhs
                  h_between_rhs]
            show ii.val - 1 + 2 = ii.val + 1
            omega
          exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx

/-- For `a < b < t`, replacing row `s` (with `s.val = t.val - 2`) of
`nMatrix B a b hab` by `B[b]` and then sliding that row up to position
`b.val - 1` by `t.val - b.val - 1` adjacent swaps reproduces
`nMatrix B a t (Nat.lt_trans hab hbt)`. -/
private theorem rowMoveUp_setRow_nMatrix_replace_second
    {R : Type u} {n : Nat} (B : Matrix R (n + 2) n)
    (a b t : Fin (n + 2)) (hab : a.val < b.val) (hbt : b.val < t.val)
    (s : Fin n) (hs : s.val = t.val - 2)
    (hsk : b.val - 1 + (t.val - b.val - 1) < n) :
    rowMoveUp (setRow (nMatrix B a b hab) s B[b]) (b.val - 1)
        (t.val - b.val - 1) hsk =
      nMatrix B a t (Nat.lt_trans hab hbt) := by
  apply Vector.ext
  intro i hi
  let ii : Fin n := ⟨i, hi⟩
  have hat : a.val < t.val := Nat.lt_trans hab hbt
  show (rowMoveUp (setRow (nMatrix B a b hab) s B[b]) (b.val - 1)
        (t.val - b.val - 1) hsk)[ii] = (nMatrix B a t hat)[ii]
  by_cases h_below : ii.val < b.val - 1
  · -- Below the move interval.
    have hii_ne_s : ii ≠ s := by
      intro he
      have hv : ii.val = s.val := congrArg Fin.val he
      rw [hs] at hv; omega
    rw [rowMoveUp_row_of_lt (setRow (nMatrix B a b hab) s B[b]) (b.val - 1)
          (t.val - b.val - 1) hsk ii h_below,
        setRow_row_ne (nMatrix B a b hab) s ii B[b] hii_ne_s]
    apply Vector.ext
    intro j hj
    let jj : Fin n := ⟨j, hj⟩
    show (nMatrix B a b hab)[ii][jj] = (nMatrix B a t hat)[ii][jj]
    rw [nMatrix_entry, nMatrix_entry]
    by_cases h_lt_a : ii.val < a.val
    · have hidx : skipIndex2 a b hab ii = skipIndex2 a t hat ii := by
        apply Fin.ext
        rw [skipIndex2_val_of_lt_p a b hab ii h_lt_a,
            skipIndex2_val_of_lt_p a t hat ii h_lt_a]
      exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx
    · have h_between_lhs : ii.val + 1 < b.val := by omega
      have h_between_rhs : ii.val + 1 < t.val := by omega
      have hidx : skipIndex2 a b hab ii = skipIndex2 a t hat ii := by
        apply Fin.ext
        rw [skipIndex2_val_of_between a b hab ii h_lt_a h_between_lhs,
            skipIndex2_val_of_between a t hat ii h_lt_a h_between_rhs]
      exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx
  · by_cases h_eq : ii.val = b.val - 1
    · -- At the source of the move: the inserted row B[b] surfaces here.
      have h_row_eq :
          (rowMoveUp (setRow (nMatrix B a b hab) s B[b]) (b.val - 1)
              (t.val - b.val - 1) hsk)[ii] = B[b] := by
        rw [rowMoveUp_row_eq_src (setRow (nMatrix B a b hab) s B[b])
              (b.val - 1) (t.val - b.val - 1) hsk ii h_eq]
        have hidx_eq :
            (⟨b.val - 1 + (t.val - b.val - 1), hsk⟩ : Fin n) = s := by
          apply Fin.ext
          show b.val - 1 + (t.val - b.val - 1) = s.val
          rw [hs]; omega
        calc (setRow (nMatrix B a b hab) s B[b])[
              (⟨b.val - 1 + (t.val - b.val - 1), hsk⟩ : Fin n)]
            = (setRow (nMatrix B a b hab) s B[b])[s] :=
              congrArg
                (fun (i : Fin n) =>
                  (setRow (nMatrix B a b hab) s B[b])[i]) hidx_eq
          _ = B[b] := setRow_get_self _ _ _
      rw [h_row_eq]
      apply Vector.ext
      intro j hj
      let jj : Fin n := ⟨j, hj⟩
      show B[b][jj] = (nMatrix B a t hat)[ii][jj]
      rw [nMatrix_entry]
      have h_not_lt_a : ¬ ii.val < a.val := by
        have : a.val ≤ b.val - 1 := by omega
        rw [h_eq]; omega
      have h_between : ii.val + 1 < t.val := by rw [h_eq]; omega
      have hidx : skipIndex2 a t hat ii = b := by
        apply Fin.ext
        rw [skipIndex2_val_of_between a t hat ii h_not_lt_a h_between]
        show ii.val + 1 = b.val
        rw [h_eq]; omega
      exact (congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx).symm
    · by_cases h_above : t.val - 2 < ii.val
      · -- Above the move interval.
        have h_above' : b.val - 1 + (t.val - b.val - 1) < ii.val := by
          have : b.val - 1 + (t.val - b.val - 1) = t.val - 2 := by omega
          rw [this]; exact h_above
        rw [rowMoveUp_row_of_gt (setRow (nMatrix B a b hab) s B[b])
              (b.val - 1) (t.val - b.val - 1) hsk ii h_above']
        have hii_ne_s : ii ≠ s := by
          intro he
          have hv : ii.val = s.val := congrArg Fin.val he
          rw [hs] at hv; omega
        rw [setRow_row_ne (nMatrix B a b hab) s ii B[b] hii_ne_s]
        apply Vector.ext
        intro j hj
        let jj : Fin n := ⟨j, hj⟩
        show (nMatrix B a b hab)[ii][jj] = (nMatrix B a t hat)[ii][jj]
        rw [nMatrix_entry, nMatrix_entry]
        have h_not_lt_a : ¬ ii.val < a.val := by omega
        have h_not_between_lhs : ¬ ii.val + 1 < b.val := by omega
        have h_not_between_rhs : ¬ ii.val + 1 < t.val := by omega
        have hidx : skipIndex2 a b hab ii = skipIndex2 a t hat ii := by
          apply Fin.ext
          rw [skipIndex2_val_of_ge_q a b hab ii h_not_lt_a h_not_between_lhs,
              skipIndex2_val_of_ge_q a t hat ii h_not_lt_a h_not_between_rhs]
        exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx
      · -- Inside the move interval (strictly).
        have h_lt_src : b.val - 1 < ii.val := by
          have h1 : ¬ ii.val < b.val - 1 := h_below
          have h2 : ii.val ≠ b.val - 1 := h_eq
          omega
        have h_le_top : ii.val ≤ b.val - 1 + (t.val - b.val - 1) := by
          have : b.val - 1 + (t.val - b.val - 1) = t.val - 2 := by omega
          rw [this]; omega
        rw [rowMoveUp_row_between (setRow (nMatrix B a b hab) s B[b])
              (b.val - 1) (t.val - b.val - 1) hsk ii h_lt_src h_le_top]
        let j_minus : Fin n := ⟨ii.val - 1, by have := ii.isLt; omega⟩
        have hj_ne_s : j_minus ≠ s := by
          intro he
          have hv : j_minus.val = s.val := congrArg Fin.val he
          rw [hs] at hv
          have : ii.val - 1 = t.val - 2 := hv
          omega
        rw [setRow_row_ne (nMatrix B a b hab) s j_minus B[b] hj_ne_s]
        apply Vector.ext
        intro j hj
        let jj : Fin n := ⟨j, hj⟩
        show (nMatrix B a b hab)[j_minus][jj] = (nMatrix B a t hat)[ii][jj]
        rw [nMatrix_entry, nMatrix_entry]
        have h_not_lt_a_lhs : ¬ j_minus.val < a.val := by
          show ¬ ii.val - 1 < a.val
          have : a.val ≤ b.val - 1 := by omega
          omega
        have h_not_between_lhs : ¬ j_minus.val + 1 < b.val := by
          show ¬ ii.val - 1 + 1 < b.val
          omega
        have h_not_lt_a_rhs : ¬ ii.val < a.val := by omega
        have h_between_rhs : ii.val + 1 < t.val := by omega
        have hidx : skipIndex2 a b hab j_minus = skipIndex2 a t hat ii := by
          apply Fin.ext
          rw [skipIndex2_val_of_ge_q a b hab j_minus h_not_lt_a_lhs
                h_not_between_lhs,
              skipIndex2_val_of_between a t hat ii h_not_lt_a_rhs
                h_between_rhs]
          show ii.val - 1 + 2 = ii.val + 1
          omega
        exact congrArg (fun (x : Fin (n + 2)) => B[x][jj]) hidx

/-- For ordered rows `r0 < r1 < r2 < r3` of `B : Matrix R (n + 2) n`,
replacing the `s2 = ⟨r2.val - 2, _⟩` row of `nMatrix B r0 r1 h01` by
`B[r0]` produces the signed `nDet B r1 r2 h12` minor with sign
`(-1) ^ (r2.val - r0.val - 2)`. -/
private theorem det_setRow_nMatrix_r2_r0
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (r0 r1 r2 r3 : Fin (n + 2))
    (h01 : r0.val < r1.val) (h12 : r1.val < r2.val) (h23 : r2.val < r3.val) :
    let M := nMatrix B r0 r1 h01
    let s2 : Fin n := ⟨r2.val - 2, by have := r3.isLt; omega⟩
    det (setRow M s2 B[r0]) =
      (-1 : R) ^ (r2.val - r0.val - 2) * nDet B r1 r2 h12 := by
  intro M s2
  have hsk : r0.val + (r2.val - r0.val - 2) < n := by
    have _h13 : r1.val < r3.val := Nat.lt_trans h12 h23
    have := r3.isLt; omega
  have hrow := rowMoveUp_setRow_nMatrix_replace_first
      B r0 r1 r2 h01 h12 s2 rfl hsk
  have hdet_rm :=
    det_rowMoveUp (setRow M s2 B[r0]) r0.val (r2.val - r0.val - 2) hsk
  rw [hrow] at hdet_rm
  show det (setRow M s2 B[r0]) =
    (-1 : R) ^ (r2.val - r0.val - 2) * nDet B r1 r2 h12
  have h_nDet : nDet B r1 r2 h12 = det (nMatrix B r1 r2 h12) := rfl
  rw [h_nDet, hdet_rm, ← Lean.Grind.Semiring.mul_assoc,
      neg_one_pow_mul_self, Lean.Grind.Semiring.one_mul]

/-- For ordered rows `r0 < r1 < r2 < r3`, replacing the
`s3 = ⟨r3.val - 2, _⟩` row of `nMatrix B r0 r1 h01` by `B[r0]` produces
the signed `nDet B r1 r3 _` minor with sign `(-1) ^ (r3.val - r0.val - 2)`. -/
private theorem det_setRow_nMatrix_r3_r0
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (r0 r1 r2 r3 : Fin (n + 2))
    (h01 : r0.val < r1.val) (h12 : r1.val < r2.val) (h23 : r2.val < r3.val) :
    let M := nMatrix B r0 r1 h01
    let s3 : Fin n := ⟨r3.val - 2, by have := r3.isLt; omega⟩
    det (setRow M s3 B[r0]) =
      (-1 : R) ^ (r3.val - r0.val - 2) *
        nDet B r1 r3 (Nat.lt_trans h12 h23) := by
  intro M s3
  have h13 : r1.val < r3.val := Nat.lt_trans h12 h23
  have hsk : r0.val + (r3.val - r0.val - 2) < n := by
    have := r3.isLt; omega
  have hrow := rowMoveUp_setRow_nMatrix_replace_first
      B r0 r1 r3 h01 h13 s3 rfl hsk
  have hdet_rm :=
    det_rowMoveUp (setRow M s3 B[r0]) r0.val (r3.val - r0.val - 2) hsk
  rw [hrow] at hdet_rm
  show det (setRow M s3 B[r0]) =
    (-1 : R) ^ (r3.val - r0.val - 2) * nDet B r1 r3 h13
  have h_nDet : nDet B r1 r3 h13 = det (nMatrix B r1 r3 h13) := rfl
  rw [h_nDet, hdet_rm, ← Lean.Grind.Semiring.mul_assoc,
      neg_one_pow_mul_self, Lean.Grind.Semiring.one_mul]

/-- For ordered rows `r0 < r1 < r2 < r3`, replacing the
`s2 = ⟨r2.val - 2, _⟩` row of `nMatrix B r0 r1 h01` by `B[r1]` produces
the signed `nDet B r0 r2 _` minor with sign `(-1) ^ (r2.val - r1.val - 1)`. -/
private theorem det_setRow_nMatrix_r2_r1
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (r0 r1 r2 r3 : Fin (n + 2))
    (h01 : r0.val < r1.val) (h12 : r1.val < r2.val) (h23 : r2.val < r3.val) :
    let M := nMatrix B r0 r1 h01
    let s2 : Fin n := ⟨r2.val - 2, by have := r3.isLt; omega⟩
    det (setRow M s2 B[r1]) =
      (-1 : R) ^ (r2.val - r1.val - 1) *
        nDet B r0 r2 (Nat.lt_trans h01 h12) := by
  intro M s2
  have h02 : r0.val < r2.val := Nat.lt_trans h01 h12
  have hsk : r1.val - 1 + (r2.val - r1.val - 1) < n := by
    have := r3.isLt; omega
  have hrow := rowMoveUp_setRow_nMatrix_replace_second
      B r0 r1 r2 h01 h12 s2 rfl hsk
  have hdet_rm :=
    det_rowMoveUp (setRow M s2 B[r1]) (r1.val - 1) (r2.val - r1.val - 1) hsk
  rw [hrow] at hdet_rm
  show det (setRow M s2 B[r1]) =
    (-1 : R) ^ (r2.val - r1.val - 1) * nDet B r0 r2 h02
  have h_nDet : nDet B r0 r2 h02 = det (nMatrix B r0 r2 h02) := rfl
  rw [h_nDet, hdet_rm, ← Lean.Grind.Semiring.mul_assoc,
      neg_one_pow_mul_self, Lean.Grind.Semiring.one_mul]

/-- For ordered rows `r0 < r1 < r2 < r3`, replacing the
`s3 = ⟨r3.val - 2, _⟩` row of `nMatrix B r0 r1 h01` by `B[r1]` produces
the signed `nDet B r0 r3 _` minor with sign `(-1) ^ (r3.val - r1.val - 1)`. -/
private theorem det_setRow_nMatrix_r3_r1
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (r0 r1 r2 r3 : Fin (n + 2))
    (h01 : r0.val < r1.val) (h12 : r1.val < r2.val) (h23 : r2.val < r3.val) :
    let M := nMatrix B r0 r1 h01
    let s3 : Fin n := ⟨r3.val - 2, by have := r3.isLt; omega⟩
    det (setRow M s3 B[r1]) =
      (-1 : R) ^ (r3.val - r1.val - 1) *
        nDet B r0 r3 (Nat.lt_trans h01 (Nat.lt_trans h12 h23)) := by
  intro M s3
  have h13 : r1.val < r3.val := Nat.lt_trans h12 h23
  have h03 : r0.val < r3.val := Nat.lt_trans h01 h13
  have hsk : r1.val - 1 + (r3.val - r1.val - 1) < n := by
    have := r3.isLt; omega
  have hrow := rowMoveUp_setRow_nMatrix_replace_second
      B r0 r1 r3 h01 h13 s3 rfl hsk
  have hdet_rm :=
    det_rowMoveUp (setRow M s3 B[r1]) (r1.val - 1) (r3.val - r1.val - 1) hsk
  rw [hrow] at hdet_rm
  show det (setRow M s3 B[r1]) =
    (-1 : R) ^ (r3.val - r1.val - 1) * nDet B r0 r3 h03
  have h_nDet : nDet B r0 r3 h03 = det (nMatrix B r0 r3 h03) := rfl
  rw [h_nDet, hdet_rm, ← Lean.Grind.Semiring.mul_assoc,
      neg_one_pow_mul_self, Lean.Grind.Semiring.one_mul]

/-! ### Double-row `setRow` transport to ordered `nDet` minors

For ordered rows `r0 < r1 < r2 < r3`, the double replacement
`setRow (setRow (nMatrix B r0 r1 h01) s2 B[r0]) s3 B[r1]` (with
`s2 = ⟨r2.val - 2, _⟩` and `s3 = ⟨r3.val - 2, _⟩`) realises the row
content of `nMatrix B r2 r3 h23` with the inserted rows `B[r0]` and
`B[r1]` displaced downward. Two `rowMoveUp` operations (first sliding
`B[r0]` up to position `r0.val`, then `B[r1]` up to position `r1.val - 1`
of the intermediate matrix) reorder the rows back, contributing the
combined sign `(-1)^((r2 - r0 - 2) + (r3 - r1 - 2))`. The intermediate
identification uses `rowMoveUp_setRow_of_gt` to slide the outer
`setRow s3 B[r1]` past the inner `rowMoveUp`, since `s3.val > r2.val - 2`
places it strictly above the inner move interval. -/

/-- `rowMoveUp` commutes with `setRow` when the `setRow` target index
sits strictly above the move interval. The destination row is untouched
by `rowMoveUp` on both sides, so the operations can be exchanged. -/
private theorem rowMoveUp_setRow_of_gt {R : Type u} {n m : Nat}
    (M : Matrix R n m) (src k : Nat) (h : src + k < n) (j : Fin n)
    (v : Vector R m) (hj : src + k < j.val) :
    rowMoveUp (setRow M j v) src k h = setRow (rowMoveUp M src k h) j v := by
  apply Vector.ext
  intro i hi
  let ii : Fin n := ⟨i, hi⟩
  show (rowMoveUp (setRow M j v) src k h)[ii] =
    (setRow (rowMoveUp M src k h) j v)[ii]
  by_cases h_eq_j : ii = j
  · -- ii = j: both sides evaluate to v
    have hii_gt : src + k < ii.val := by
      have := congrArg Fin.val h_eq_j; omega
    have hLHS_move :
        (rowMoveUp (setRow M j v) src k h)[ii] = (setRow M j v)[ii] :=
      rowMoveUp_row_of_gt (setRow M j v) src k h ii hii_gt
    have hLHS_idx :
        (setRow M j v)[ii] = (setRow M j v)[j] :=
      congrArg (fun (i : Fin n) => (setRow M j v)[i]) h_eq_j
    have hRHS_idx :
        (setRow (rowMoveUp M src k h) j v)[ii] =
          (setRow (rowMoveUp M src k h) j v)[j] :=
      congrArg (fun (i : Fin n) =>
        (setRow (rowMoveUp M src k h) j v)[i]) h_eq_j
    rw [hLHS_move, hLHS_idx, hRHS_idx, setRow_get_self, setRow_get_self]
  · -- ii ≠ j: the outer setRow on the RHS is a no-op at ii
    rw [setRow_row_ne (rowMoveUp M src k h) j ii v h_eq_j]
    by_cases h_below : ii.val < src
    · -- Below the move interval: both rowMoveUp ops are no-ops at ii
      rw [rowMoveUp_row_of_lt (setRow M j v) src k h ii h_below,
          rowMoveUp_row_of_lt M src k h ii h_below,
          setRow_row_ne M j ii v h_eq_j]
    · by_cases h_eq_src : ii.val = src
      · -- ii.val = src: rowMoveUp produces the row originally at src + k
        rw [rowMoveUp_row_eq_src (setRow M j v) src k h ii h_eq_src,
            rowMoveUp_row_eq_src M src k h ii h_eq_src]
        have hsk_ne_j : (⟨src + k, h⟩ : Fin n) ≠ j := by
          intro he
          have : src + k = j.val := congrArg Fin.val he
          omega
        rw [setRow_row_ne M j ⟨src + k, h⟩ v hsk_ne_j]
      · by_cases h_above : src + k < ii.val
        · -- Above the move interval: both rowMoveUp ops are no-ops at ii
          rw [rowMoveUp_row_of_gt (setRow M j v) src k h ii h_above,
              rowMoveUp_row_of_gt M src k h ii h_above,
              setRow_row_ne M j ii v h_eq_j]
        · -- Strictly inside: src < ii.val ≤ src + k; both rowMoveUp ops
          -- produce the row originally at ii.val - 1
          have h_lt_src : src < ii.val := by
            have h1 : ¬ ii.val < src := h_below
            have h2 : ii.val ≠ src := h_eq_src
            omega
          have h_le_top : ii.val ≤ src + k := by omega
          rw [rowMoveUp_row_between (setRow M j v) src k h ii h_lt_src h_le_top,
              rowMoveUp_row_between M src k h ii h_lt_src h_le_top]
          have h_iminus_ne_j :
              (⟨ii.val - 1, by have := ii.isLt; omega⟩ : Fin n) ≠ j := by
            intro he
            have : ii.val - 1 = j.val := congrArg Fin.val he
            omega
          rw [setRow_row_ne M j ⟨ii.val - 1, by have := ii.isLt; omega⟩
                v h_iminus_ne_j]

/-- For ordered rows `r0 < r1 < r2 < r3`, the doubly-replaced matrix
`setRow (setRow (nMatrix B r0 r1 h01) s2 B[r0]) s3 B[r1]` (with
`s2 = ⟨r2.val - 2, _⟩` and `s3 = ⟨r3.val - 2, _⟩`) has determinant
`(-1)^((r2 - r0 - 2) + (r3 - r1 - 2)) * nDet B r2 r3 h23`. -/
private theorem det_setRow_setRow_nMatrix_r2_r0_r3_r1
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (r0 r1 r2 r3 : Fin (n + 2))
    (h01 : r0.val < r1.val) (h12 : r1.val < r2.val)
    (h23 : r2.val < r3.val) :
    let M := nMatrix B r0 r1 h01
    let s2 : Fin n := ⟨r2.val - 2, by have := r3.isLt; omega⟩
    let s3 : Fin n := ⟨r3.val - 2, by have := r3.isLt; omega⟩
    det (setRow (setRow M s2 B[r0]) s3 B[r1]) =
      (-1 : R) ^ ((r2.val - r0.val - 2) + (r3.val - r1.val - 2)) *
        nDet B r2 r3 h23 := by
  intro M s2 s3
  have hsk1 : r0.val + (r2.val - r0.val - 2) < n := by
    have := r3.isLt; omega
  have hsk2 : r1.val + (r3.val - r1.val - 2) < n := by
    have := r3.isLt; omega
  have hs3_gt : r0.val + (r2.val - r0.val - 2) < s3.val := by
    show r0.val + (r2.val - r0.val - 2) < r3.val - 2
    omega
  -- Step 1: slide the outer `setRow s3 B[r1]` past the first `rowMoveUp`.
  have hcommute :
      rowMoveUp (setRow (setRow M s2 B[r0]) s3 B[r1]) r0.val
          (r2.val - r0.val - 2) hsk1 =
        setRow
          (rowMoveUp (setRow M s2 B[r0]) r0.val (r2.val - r0.val - 2) hsk1)
          s3 B[r1] :=
    rowMoveUp_setRow_of_gt (setRow M s2 B[r0]) r0.val (r2.val - r0.val - 2)
      hsk1 s3 B[r1] hs3_gt
  -- Step 2: identify the inner `rowMoveUp` with `nMatrix B r1 r2 h12`.
  have hrow1 :
      rowMoveUp (setRow M s2 B[r0]) r0.val (r2.val - r0.val - 2) hsk1 =
        nMatrix B r1 r2 h12 :=
    rowMoveUp_setRow_nMatrix_replace_first
      B r0 r1 r2 h01 h12 s2 rfl hsk1
  rw [hrow1] at hcommute
  -- Step 3: outer `det_rowMoveUp` peels off the first sign factor.
  have hdet_outer :=
    det_rowMoveUp (setRow (setRow M s2 B[r0]) s3 B[r1]) r0.val
      (r2.val - r0.val - 2) hsk1
  rw [hcommute] at hdet_outer
  -- hdet_outer : det (setRow (nMatrix B r1 r2 h12) s3 B[r1]) =
  --              (-1)^(r2 - r0 - 2) * det (setRow (setRow M s2 B[r0]) s3 B[r1])
  -- Step 4: identify the next `rowMoveUp` with `nMatrix B r2 r3 h23`.
  have hrow2 :
      rowMoveUp (setRow (nMatrix B r1 r2 h12) s3 B[r1]) r1.val
          (r3.val - r1.val - 2) hsk2 =
        nMatrix B r2 r3 h23 :=
    rowMoveUp_setRow_nMatrix_replace_first
      B r1 r2 r3 h12 h23 s3 rfl hsk2
  -- Step 5: inner `det_rowMoveUp` peels off the second sign factor.
  have hdet_inner :=
    det_rowMoveUp (setRow (nMatrix B r1 r2 h12) s3 B[r1]) r1.val
      (r3.val - r1.val - 2) hsk2
  rw [hrow2] at hdet_inner
  -- hdet_inner : det (nMatrix B r2 r3 h23) =
  --              (-1)^(r3 - r1 - 2) * det (setRow (nMatrix B r1 r2 h12) s3 B[r1])
  -- Combine. Let a = r2 - r0 - 2, b = r3 - r1 - 2. After substitution we
  -- need D = (-1)^(a+b) * ((-1)^b * ((-1)^a * D)), which collapses by
  -- `pow_add` and `neg_one_pow_mul_self`.
  show det (setRow (setRow M s2 B[r0]) s3 B[r1]) =
    (-1 : R) ^ ((r2.val - r0.val - 2) + (r3.val - r1.val - 2)) *
      nDet B r2 r3 h23
  have h_nDet : nDet B r2 r3 h23 = det (nMatrix B r2 r3 h23) := rfl
  rw [h_nDet, hdet_inner, hdet_outer]
  have h_pow_add :
      (-1 : R) ^ ((r2.val - r0.val - 2) + (r3.val - r1.val - 2)) =
        (-1 : R) ^ (r2.val - r0.val - 2) *
          (-1 : R) ^ (r3.val - r1.val - 2) :=
    Lean.Grind.Semiring.pow_add (-1 : R) (r2.val - r0.val - 2)
      (r3.val - r1.val - 2)
  have h_self_a := neg_one_pow_mul_self (R := R) (r2.val - r0.val - 2)
  have h_self_b := neg_one_pow_mul_self (R := R) (r3.val - r1.val - 2)
  rw [h_pow_add]
  grind

/-- The square matrix `[B | u | v]` formed by appending two vector columns to
`B : Matrix R (n + 2) n`. The original `B` columns occupy positions
`0..n-1`; `u` occupies column `n`; `v` occupies the last column. -/
@[expose]
def twoColMatrix {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2)) :
    Matrix R (n + 2) (n + 2) :=
  ofFn fun i j =>
    if hj : j.val < n then
      B[i][(⟨j.val, hj⟩ : Fin n)]
    else if hju : j.val = n then
      u[i]
    else
      v[i]

/-- In one of the original `B` columns, `twoColMatrix` agrees entrywise with
`B`. -/
theorem twoColMatrix_entry_lt {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2))
    (i j : Fin (n + 2)) (h : j.val < n) :
    (twoColMatrix B u v)[i][j] = B[i][(⟨j.val, h⟩ : Fin n)] := by
  unfold twoColMatrix
  rw [getElem_ofFn]
  exact dif_pos h

/-- The penultimate column of `twoColMatrix B u v` is `u`. -/
theorem twoColMatrix_entry_penultimate {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2))
    (i : Fin (n + 2)) :
    (twoColMatrix B u v)[i][(⟨n, by omega⟩ : Fin (n + 2))] = u[i] := by
  unfold twoColMatrix
  rw [getElem_ofFn]
  have hnlt : ¬ (⟨n, by omega⟩ : Fin (n + 2)).val < n := by
    simp
  have hneq : (⟨n, by omega⟩ : Fin (n + 2)).val = n := by
    simp
  rw [dif_neg hnlt]
  rw [dif_pos hneq]

/-- The last column of `twoColMatrix B u v` is `v`. -/
theorem twoColMatrix_entry_last {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2))
    (i : Fin (n + 2)) :
    (twoColMatrix B u v)[i][Fin.last (n + 1)] = v[i] := by
  unfold twoColMatrix
  rw [getElem_ofFn]
  have hlast_lt : ¬ (Fin.last (n + 1) : Fin (n + 2)).val < n := by
    simp [Fin.last]
  have hlast_ne : ¬ (Fin.last (n + 1) : Fin (n + 2)).val = n := by
    simp [Fin.last]
  rw [dif_neg hlast_lt]
  rw [dif_neg hlast_ne]

/-- The determinant of `[B | u | v]`. -/
@[expose]
def twoColDet {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2)) : R :=
  det (twoColMatrix B u v)

/-- Deleting row `p` and the final `v` column from `[B | u | v]`
recovers the one-column augmented matrix `mMatrix B u p`. -/
theorem deleteRowCol_twoColMatrix_last_eq_mMatrix {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2)) (p : Fin (n + 2)) :
    deleteRowCol (twoColMatrix B u v) p (Fin.last (n + 1)) =
      mMatrix B u p := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin (n + 1) := ⟨i, hi⟩
  let jj : Fin (n + 1) := ⟨j, hj⟩
  change (deleteRowCol (twoColMatrix B u v) p (Fin.last (n + 1)))[ii][jj] =
    (mMatrix B u p)[ii][jj]
  rw [deleteRowCol_entry]
  have hcol :
      (skipIndex (Fin.last (n + 1)) jj).val = jj.val := by
    rw [skipIndex_last]
    simp
  by_cases hjlt : jj.val < n
  · have hskiplt : (skipIndex (Fin.last (n + 1)) jj).val < n := by
      rw [hcol]
      exact hjlt
    rw [twoColMatrix_entry_lt B u v (skipIndex p ii)
        (skipIndex (Fin.last (n + 1)) jj) hskiplt]
    rw [mMatrix_entry_lt B u p ii jj hjlt]
    have hcol_eq : (⟨(skipIndex (Fin.last (n + 1)) jj).val, hskiplt⟩ : Fin n) =
        (⟨jj.val, hjlt⟩ : Fin n) := by
      apply Fin.ext
      exact hcol
    simp only [hcol_eq]
  · have hjn : jj.val = n := by omega
    have hskip_eq :
        skipIndex (Fin.last (n + 1)) jj =
          (⟨n, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rw [hcol]
      exact hjn
    have hjj_last : jj = Fin.last n := by
      apply Fin.ext
      simp [Fin.last, hjn]
    calc
      (twoColMatrix B u v)[skipIndex p ii][skipIndex (Fin.last (n + 1)) jj] =
          (twoColMatrix B u v)[skipIndex p ii][(⟨n, by omega⟩ : Fin (n + 2))] := by
            exact congrArg (fun c => (twoColMatrix B u v)[skipIndex p ii][c]) hskip_eq
      _ = u[skipIndex p ii] := by
            exact twoColMatrix_entry_penultimate B u v (skipIndex p ii)
      _ = (mMatrix B u p)[ii][jj] := by
            calc
              u[skipIndex p ii] = (mMatrix B u p)[ii][Fin.last n] := by
                exact (mMatrix_entry_last B u p ii).symm
              _ = (mMatrix B u p)[ii][jj] := by
                exact (congrArg (fun c => (mMatrix B u p)[ii][c]) hjj_last).symm

/-- Laplace expansion of the two-column determinant along the final column,
with the remaining minor identified as `mDet B u p`. -/
theorem twoColDet_eq_sum_mDet {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2)) :
    twoColDet B u v =
      (List.finRange (n + 2)).foldl
        (fun acc p =>
          acc + v[p] * (cofactorSign (R := R) p (Fin.last (n + 1)) * mDet B u p)) 0 := by
  unfold twoColDet
  rw [det_eq_foldl_laplace_last (twoColMatrix B u v)]
  apply foldl_acc_congr
  intro acc p _hmem
  rw [twoColMatrix_entry_last]
  unfold cofactor mDet
  rw [deleteRowCol_twoColMatrix_last_eq_mMatrix B u v p]

/-- `mMatrix B v p` exposed as a `colReplace` on its last column: the
other columns come from `B` and are independent of `v`, while the last
column carries `fun i => v[skipIndex p i]`. -/
theorem mMatrix_eq_colReplace_last {R : Type u} {n : Nat}
    (B : Matrix R (n + 2) n) (v w : Vector R (n + 2)) (p : Fin (n + 2)) :
    mMatrix B v p =
      colReplace (mMatrix B w p) (Fin.last n)
        (fun i : Fin (n + 1) => v[skipIndex p i]) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  change (mMatrix B v p)[(⟨i, hi⟩ : Fin (n + 1))][(⟨j, hj⟩ : Fin (n + 1))] =
    (colReplace (mMatrix B w p) (Fin.last n)
        (fun i : Fin (n + 1) => v[skipIndex p i]))[(⟨i, hi⟩ : Fin (n + 1))][(⟨j, hj⟩ : Fin (n + 1))]
  rw [colReplace_get]
  by_cases hjlt : j < n
  · have hjne : (⟨j, hj⟩ : Fin (n + 1)) ≠ Fin.last n := by
      intro h
      have hval := congrArg Fin.val h
      simp [Fin.last] at hval
      omega
    rw [if_neg hjne]
    rw [mMatrix_entry_lt B v p (⟨i, hi⟩ : Fin (n + 1)) (⟨j, hj⟩ : Fin (n + 1)) hjlt]
    rw [mMatrix_entry_lt B w p (⟨i, hi⟩ : Fin (n + 1)) (⟨j, hj⟩ : Fin (n + 1)) hjlt]
  · have hjeq : j = n := by omega
    have hjlast : (⟨j, hj⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext
      simp [Fin.last, hjeq]
    rw [if_pos hjlast]
    show (mMatrix B v p)[(⟨i, hi⟩ : Fin (n + 1))][(⟨j, hj⟩ : Fin (n + 1))] = v[skipIndex p (⟨i, hi⟩ : Fin (n + 1))]
    unfold mMatrix
    rw [getElem_ofFn]
    have hjnlt : ¬ (⟨j, hj⟩ : Fin (n + 1)).val < n := by
      show ¬ j < n; exact hjlt
    exact dif_neg hjnlt

/-- `mDet` is additive in the augmented vector column. -/
theorem mDet_add_v {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (v w : Vector R (n + 2)) (p : Fin (n + 2)) :
    mDet B (v + w) p = mDet B v p + mDet B w p := by
  unfold mDet
  rw [mMatrix_eq_colReplace_last B (v + w) v p]
  rw [show (fun i : Fin (n + 1) => (v + w)[skipIndex p i]) =
      fun i : Fin (n + 1) => v[skipIndex p i] + w[skipIndex p i] by
        funext i
        simp [Vector.getElem_add]]
  rw [det_colReplace_add]
  rw [← mMatrix_eq_colReplace_last B v v p]
  rw [← mMatrix_eq_colReplace_last B w v p]

/-- `mDet` is homogeneous in the augmented vector column. -/
theorem mDet_smul_v {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (c : R) (v : Vector R (n + 2)) (p : Fin (n + 2)) :
    mDet B (c • v) p = c * mDet B v p := by
  unfold mDet
  rw [mMatrix_eq_colReplace_last B (c • v) v p]
  rw [show (fun i : Fin (n + 1) => (c • v)[skipIndex p i]) =
      fun i : Fin (n + 1) => c * v[skipIndex p i] by
        funext i
        simp [Vector.getElem_smul]
        change c * v[skipIndex p i] = c * v[skipIndex p i]
        rfl]
  rw [det_colReplace_smul]
  rw [← mMatrix_eq_colReplace_last B v v p]

/-- The standard basis vector `e_q : Vector R (n + 2)` with value `1`
at position `q` and `0` elsewhere. -/
@[expose]
def basisVec {R : Type u} [Zero R] [One R] {n : Nat} (q : Fin (n + 2)) :
    Vector R (n + 2) :=
  Vector.ofFn fun i => if i = q then (1 : R) else (0 : R)

/-- Entry `i` of the standard basis vector `e_q` is `1` when `i = q` and `0`
otherwise. -/
@[grind =] theorem basisVec_getElem {R : Type u} [Zero R] [One R] {n : Nat}
    (q : Fin (n + 2)) (i : Fin (n + 2)) :
    (basisVec (R := R) q)[i] = if i = q then (1 : R) else (0 : R) := by
  simp [basisVec]

/-- For `p < q`, the unique row of `Fin (n + 1)` that maps to `q` under
`skipIndex p` is `⟨q.val - 1, _⟩`. -/
theorem skipIndex_at_q_minus_one_eq_q_of_lt {n : Nat}
    (p q : Fin (n + 2)) (hpq : p.val < q.val) :
    skipIndex p (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) = q := by
  apply Fin.ext
  show (skipIndex p (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1))).val = q.val
  have hnot : ¬ ((⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)).val < p.val) := by
    show ¬ q.val - 1 < p.val
    omega
  rw [skipIndex_val_of_not_lt p _ hnot]
  show q.val - 1 + 1 = q.val
  omega

/-- For `p < q`, the chained skip `skipIndex p ∘ skipIndex r_q`
(where `r_q = q.val - 1`) equals `skipIndex2 p q hpq`. This is the
row-reindexing identity used to recover the `n × n` minor of `B` from
the deleted-row-and-last-column minor of `mMatrix B (basisVec q) p`. -/
theorem skipIndex_skipIndex_eq_skipIndex2_of_lt {n : Nat}
    (p q : Fin (n + 2)) (hpq : p.val < q.val) (i : Fin n) :
    skipIndex p
        (skipIndex (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) i) =
      skipIndex2 p q hpq i := by
  apply Fin.ext
  by_cases h1 : i.val < p.val
  · have hrq : i.val < q.val - 1 := by omega
    rw [skipIndex2_val_of_lt_p p q hpq i h1]
    have hskip1 : skipIndex (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) i =
        ⟨i.val, by have := i.isLt; omega⟩ := by
      apply Fin.ext
      show (skipIndex _ i).val = i.val
      have : i.val < (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)).val := by
        show i.val < q.val - 1
        omega
      rw [skipIndex_val_of_lt _ _ this]
    rw [hskip1]
    show (skipIndex p (⟨i.val, _⟩ : Fin (n + 1))).val = i.val
    have hp : (⟨i.val, by have := i.isLt; omega⟩ : Fin (n + 1)).val < p.val := h1
    rw [skipIndex_val_of_lt p _ hp]
  · by_cases h2 : i.val + 1 < q.val
    · rw [skipIndex2_val_of_between p q hpq i h1 h2]
      have hrq_lt : i.val < q.val - 1 := by omega
      have hskip1 : skipIndex (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) i =
          ⟨i.val, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        show (skipIndex _ i).val = i.val
        have : i.val < (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)).val := by
          show i.val < q.val - 1
          omega
        rw [skipIndex_val_of_lt _ _ this]
      rw [hskip1]
      show (skipIndex p (⟨i.val, _⟩ : Fin (n + 1))).val = i.val + 1
      have hp : ¬ (⟨i.val, by have := i.isLt; omega⟩ : Fin (n + 1)).val < p.val := h1
      rw [skipIndex_val_of_not_lt p _ hp]
    · rw [skipIndex2_val_of_ge_q p q hpq i h1 h2]
      have hrq_ge : ¬ i.val < q.val - 1 := by omega
      have hskip1 : skipIndex (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) i =
          ⟨i.val + 1, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        show (skipIndex _ i).val = i.val + 1
        have : ¬ i.val < (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)).val := by
          show ¬ i.val < q.val - 1
          exact hrq_ge
        rw [skipIndex_val_of_not_lt _ _ this]
      rw [hskip1]
      show (skipIndex p (⟨i.val + 1, _⟩ : Fin (n + 1))).val = i.val + 2
      have hp : ¬ (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (n + 1)).val < p.val := by
        show ¬ i.val + 1 < p.val
        omega
      rw [skipIndex_val_of_not_lt p _ hp]

/-- Foldl over a list whose body is identically zero leaves the seed
unchanged. -/
private theorem foldl_add_zero_body {α : Type u} [Lean.Grind.CommRing α]
    {β : Type v} (xs : List β) (z : α) (f : β → α)
    (hall : ∀ y ∈ xs, f y = 0) :
    xs.foldl (fun acc y => acc + f y) z = z := by
  induction xs generalizing z with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.foldl_cons]
      have hy : f y = 0 := hall y List.mem_cons_self
      rw [hy]
      have hzero : z + (0 : α) = z := by grind
      rw [hzero]
      exact ih z (fun w hw => hall w (List.mem_cons_of_mem _ hw))

/-- Foldl over a `Nodup` list where the additive contribution is
nonzero at exactly one matching element. -/
private theorem foldl_add_with_unique_match {α : Type u}
    [Lean.Grind.CommRing α] {β : Type v} [DecidableEq β]
    (xs : List β) (z : α) (q : β) (f : β → α)
    (hmem : q ∈ xs) (hnodup : xs.Nodup) :
    xs.foldl (fun acc x => acc + (if x = q then f x else (0 : α))) z = z + f q := by
  induction xs generalizing z with
  | nil => simp at hmem
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hxq : x = q
      · -- x = q. By nodup, q ∉ xs, so the remaining foldl preserves z + f x.
        subst hxq
        rw [if_pos rfl]
        have hxs_nomem : x ∉ xs := (List.nodup_cons.mp hnodup).1
        apply foldl_add_zero_body xs (z + f x)
            (fun y => if y = x then f y else (0 : α))
        intro y hy
        have hyne : y ≠ x := fun heq => hxs_nomem (heq ▸ hy)
        exact if_neg hyne
      · -- x ≠ q. q still in xs; apply IH.
        rw [if_neg hxq]
        have hzero_step : z + (0 : α) = z := by grind
        rw [hzero_step]
        have hmem' : q ∈ xs := by
          cases List.mem_cons.mp hmem with
          | inl h => exact absurd h.symm hxq
          | inr h => exact h
        have hnodup' : xs.Nodup := (List.nodup_cons.mp hnodup).2
        exact ih z hmem' hnodup'

private theorem foldl_basisVec_weighted_single
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (q : Fin (n + 2)) (f : Fin (n + 2) → R) :
    (List.finRange (n + 2)).foldl
        (fun acc p => acc + (basisVec (R := R) q)[p] * f p) 0 =
      f q := by
  have hfold :=
    foldl_add_with_unique_match (α := R) (List.finRange (n + 2)) (0 : R) q
      (fun p => (basisVec (R := R) q)[p] * f p)
      (List.mem_finRange q) (List.nodup_finRange (n + 2))
  have hcongr :
      (List.finRange (n + 2)).foldl
          (fun acc p => acc + (basisVec (R := R) q)[p] * f p) 0 =
        (List.finRange (n + 2)).foldl
          (fun acc p =>
            acc + if p = q then (basisVec (R := R) q)[p] * f p else 0) 0 := by
    apply foldl_acc_congr
    intro acc p _hmem
    by_cases hp : p = q
    · rw [if_pos hp]
    · rw [if_neg hp]
      rw [basisVec_getElem]
      rw [if_neg hp]
      grind
  calc
    (List.finRange (n + 2)).foldl
        (fun acc p => acc + (basisVec (R := R) q)[p] * f p) 0 =
      (List.finRange (n + 2)).foldl
        (fun acc p =>
          acc + if p = q then (basisVec (R := R) q)[p] * f p else 0) 0 := hcongr
    _ = 0 + (basisVec (R := R) q)[q] * f q := hfold
    _ = f q := by
      rw [basisVec_getElem]
      rw [if_pos rfl]
      grind

/-- Expands the augmented vector column of `mDet` in the standard basis. -/
theorem mDet_eq_sum_basisVec
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (v : Vector R (n + 2)) (p : Fin (n + 2)) :
    mDet B v p =
      (List.finRange (n + 2)).foldl
        (fun acc q => acc + v[q] * mDet B (basisVec (R := R) q) p) 0 := by
  unfold mDet
  rw [mMatrix_eq_colReplace_last B v v p]
  have hcol :
      (fun i : Fin (n + 1) => v[skipIndex p i]) =
        fun i : Fin (n + 1) =>
          (List.finRange (n + 2)).foldl
            (fun acc q => acc + v[q] * (basisVec (R := R) q)[skipIndex p i]) 0 := by
    funext i
    have hfold :=
      foldl_add_with_unique_match (α := R) (List.finRange (n + 2)) (0 : R)
        (skipIndex p i)
        (fun q => v[q] * (basisVec (R := R) q)[skipIndex p i])
        (List.mem_finRange (skipIndex p i)) (List.nodup_finRange (n + 2))
    have hcongr :
        (List.finRange (n + 2)).foldl
            (fun acc q => acc + v[q] * (basisVec (R := R) q)[skipIndex p i]) 0 =
          (List.finRange (n + 2)).foldl
            (fun acc q =>
              acc + if q = skipIndex p i then
                v[q] * (basisVec (R := R) q)[skipIndex p i] else 0) 0 := by
      apply foldl_acc_congr
      intro acc q _hmem
      by_cases hq : q = skipIndex p i
      · rw [if_pos hq]
      · rw [if_neg hq]
        rw [basisVec_getElem]
        rw [if_neg (fun h => hq h.symm)]
        grind
    symm
    calc
      (List.finRange (n + 2)).foldl
          (fun acc q => acc + v[q] * (basisVec (R := R) q)[skipIndex p i]) 0 =
        (List.finRange (n + 2)).foldl
          (fun acc q =>
            acc + if q = skipIndex p i then
              v[q] * (basisVec (R := R) q)[skipIndex p i] else 0) 0 := hcongr
      _ = 0 + v[skipIndex p i] * (basisVec (R := R) (skipIndex p i))[skipIndex p i] := hfold
      _ = v[skipIndex p i] := by
        rw [basisVec_getElem]
        rw [if_pos rfl]
        grind
  rw [hcol]
  rw [det_colReplace_sum_finRange]
  apply foldl_acc_congr
  intro acc q _hmem
  rw [← mMatrix_eq_colReplace_last B (basisVec (R := R) q) v p]

/-- Laplace expansion specialized to a column equal to a standard basis
vector: if column `c` of `M` holds `1` at row `q` and `0` elsewhere, then
`det M` equals the signed minor `cofactorSign q c * det (deleteRowCol M q c)`. -/
theorem det_eq_signed_minor_of_col_basis
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (q c : Fin (n + 1))
    (hcol : ∀ r : Fin (n + 1), M[r][c] = if r = q then (1 : R) else (0 : R)) :
    det M = cofactorSign q c * det (deleteRowCol M q c) := by
  rw [det_eq_foldl_laplace_col M c]
  -- Rewrite the body using hcol; only the q-th term survives.
  have hbody : ∀ acc row,
      acc + M[row][c] * cofactor M row c =
        acc + (if row = q then cofactor M q c else (0 : R)) := by
    intro acc row
    rw [hcol row]
    by_cases h : row = q
    · subst h
      rw [if_pos rfl, if_pos rfl]
      grind
    · rw [if_neg h, if_neg h]
      grind
  have hfold :
      (List.finRange (n + 1)).foldl
          (fun acc row => acc + M[row][c] * cofactor M row c) 0 =
        (List.finRange (n + 1)).foldl
          (fun acc row =>
            acc + (if row = q then cofactor M q c else (0 : R))) 0 := by
    apply foldl_acc_congr
    intro acc row _hmem
    exact hbody acc row
  rw [hfold]
  have hmem : q ∈ List.finRange (n + 1) := List.mem_finRange q
  have hnodup : (List.finRange (n + 1)).Nodup := List.nodup_finRange (n + 1)
  rw [foldl_add_with_unique_match (List.finRange (n + 1)) (0 : R) q
        (fun _ => cofactor M q c) hmem hnodup]
  -- Now goal: 0 + cofactor M q c = cofactorSign q c * det (deleteRowCol M q c).
  rw [show (0 : R) + cofactor M q c = cofactor M q c by grind]
  rfl

/-- For `p < q`, deleting row `r_q = q.val - 1` and the last column of
`mMatrix B v p` recovers `nMatrix B p q hpq`, independent of `v`. -/
theorem deleteRowCol_mMatrix_at_q_minus_one_eq_nMatrix_of_lt
    {R : Type u} {n : Nat} (B : Matrix R (n + 2) n) (v : Vector R (n + 2))
    (p q : Fin (n + 2)) (hpq : p.val < q.val) :
    deleteRowCol (mMatrix B v p)
        (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) (Fin.last n) =
      nMatrix B p q hpq := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  change (deleteRowCol (mMatrix B v p)
        (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) (Fin.last n))[ii][jj] =
    (nMatrix B p q hpq)[ii][jj]
  rw [deleteRowCol_entry]
  rw [nMatrix_entry]
  -- The column index: skipIndex (Fin.last n) jj = jj.castSucc; its val = jj.val < n.
  have hjj_castSucc : (skipIndex (Fin.last n) jj).val = jj.val := by
    show (skipIndex (Fin.last n) jj).val = jj.val
    rw [skipIndex_last]
    simp
  have hjjlt : (skipIndex (Fin.last n) jj).val < n := by
    rw [hjj_castSucc]; exact jj.isLt
  rw [mMatrix_entry_lt B v p (skipIndex (⟨q.val - 1, _⟩ : Fin (n + 1)) ii)
        (skipIndex (Fin.last n) jj) hjjlt]
  -- Both row and column indices match the nMatrix indexing.
  have hrow : skipIndex p
        (skipIndex (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) ii) =
      skipIndex2 p q hpq ii :=
    skipIndex_skipIndex_eq_skipIndex2_of_lt p q hpq ii
  have hcol : (⟨(skipIndex (Fin.last n) jj).val, hjjlt⟩ : Fin n) = jj := by
    apply Fin.ext
    show (skipIndex (Fin.last n) jj).val = jj.val
    exact hjj_castSucc
  -- Use simp to handle index-rewriting with proof-irrelevance.
  simp only [hrow, hcol]

/-- For `q < p`, the unique row of `Fin (n + 1)` that maps to `q` under
`skipIndex p` is `⟨q.val, _⟩`. -/
theorem skipIndex_at_q_eq_q_of_gt {n : Nat}
    (p q : Fin (n + 2)) (hqp : q.val < p.val) :
    skipIndex p (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) = q := by
  apply Fin.ext
  show (skipIndex p (⟨q.val, _⟩ : Fin (n + 1))).val = q.val
  have h : (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)).val < p.val := hqp
  rw [skipIndex_val_of_lt p _ h]

/-- For `q < p`, the chained skip `skipIndex p ∘ skipIndex r_q`
(where `r_q = ⟨q.val, _⟩`) equals `skipIndex2 q p hqp`. -/
theorem skipIndex_skipIndex_eq_skipIndex2_of_gt {n : Nat}
    (p q : Fin (n + 2)) (hqp : q.val < p.val) (i : Fin n) :
    skipIndex p
        (skipIndex (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) i) =
      skipIndex2 q p hqp i := by
  apply Fin.ext
  by_cases h1 : i.val < q.val
  · rw [skipIndex2_val_of_lt_p q p hqp i h1]
    have hskip1 : skipIndex (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) i =
        ⟨i.val, by have := i.isLt; omega⟩ := by
      apply Fin.ext
      show (skipIndex _ i).val = i.val
      have : i.val < (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)).val := h1
      rw [skipIndex_val_of_lt _ _ this]
    rw [hskip1]
    show (skipIndex p (⟨i.val, _⟩ : Fin (n + 1))).val = i.val
    have hp : (⟨i.val, by have := i.isLt; omega⟩ : Fin (n + 1)).val < p.val := by
      show i.val < p.val
      omega
    rw [skipIndex_val_of_lt p _ hp]
  · by_cases h2 : i.val + 1 < p.val
    · rw [skipIndex2_val_of_between q p hqp i h1 h2]
      have hskip1 : skipIndex (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) i =
          ⟨i.val + 1, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        show (skipIndex _ i).val = i.val + 1
        have hne : ¬ i.val < (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)).val := h1
        rw [skipIndex_val_of_not_lt _ _ hne]
      rw [hskip1]
      show (skipIndex p (⟨i.val + 1, _⟩ : Fin (n + 1))).val = i.val + 1
      have hp : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (n + 1)).val < p.val := h2
      rw [skipIndex_val_of_lt p _ hp]
    · rw [skipIndex2_val_of_ge_q q p hqp i h1 h2]
      have hskip1 : skipIndex (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) i =
          ⟨i.val + 1, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        show (skipIndex _ i).val = i.val + 1
        have hne : ¬ i.val < (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)).val := h1
        rw [skipIndex_val_of_not_lt _ _ hne]
      rw [hskip1]
      show (skipIndex p (⟨i.val + 1, _⟩ : Fin (n + 1))).val = i.val + 2
      have hp : ¬ (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (n + 1)).val < p.val := h2
      rw [skipIndex_val_of_not_lt p _ hp]

/-- For `q < p`, deleting row `r_q = q.val` and the last column of
`mMatrix B v p` recovers `nMatrix B q p hqp`, independent of `v`. -/
theorem deleteRowCol_mMatrix_at_q_eq_nMatrix_of_gt
    {R : Type u} {n : Nat} (B : Matrix R (n + 2) n) (v : Vector R (n + 2))
    (p q : Fin (n + 2)) (hqp : q.val < p.val) :
    deleteRowCol (mMatrix B v p)
        (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) (Fin.last n) =
      nMatrix B q p hqp := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  change (deleteRowCol (mMatrix B v p)
        (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) (Fin.last n))[ii][jj] =
    (nMatrix B q p hqp)[ii][jj]
  rw [deleteRowCol_entry]
  rw [nMatrix_entry]
  have hjj_castSucc : (skipIndex (Fin.last n) jj).val = jj.val := by
    show (skipIndex (Fin.last n) jj).val = jj.val
    rw [skipIndex_last]
    simp
  have hjjlt : (skipIndex (Fin.last n) jj).val < n := by
    rw [hjj_castSucc]; exact jj.isLt
  rw [mMatrix_entry_lt B v p (skipIndex (⟨q.val, _⟩ : Fin (n + 1)) ii)
        (skipIndex (Fin.last n) jj) hjjlt]
  have hrow : skipIndex p
        (skipIndex (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) ii) =
      skipIndex2 q p hqp ii :=
    skipIndex_skipIndex_eq_skipIndex2_of_gt p q hqp ii
  have hcol : (⟨(skipIndex (Fin.last n) jj).val, hjjlt⟩ : Fin n) = jj := by
    apply Fin.ext
    show (skipIndex (Fin.last n) jj).val = jj.val
    exact hjj_castSucc
  simp only [hrow, hcol]

/-- Basis-vector evaluation of `mDet` when `q < p`: the basis vector
`e_q` becomes the standard basis vector `e_{q.val}` in the last
column of `mMatrix B (basisVec q) p`, so Laplace along that column
recovers a signed `n × n` minor of `B`. -/
theorem mDet_basisVec_eq_signed_nDet_of_gt
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (p q : Fin (n + 2)) (hqp : q.val < p.val) :
    mDet B (basisVec (R := R) q) p =
      cofactorSign (R := R)
        (⟨q.val, by have := p.isLt; omega⟩ : Fin (n + 1)) (Fin.last n) *
      nDet B q p hqp := by
  unfold mDet
  let r_q : Fin (n + 1) := ⟨q.val, by have := p.isLt; omega⟩
  show (mMatrix B (basisVec (R := R) q) p).det =
      cofactorSign (R := R) r_q (Fin.last n) * nDet B q p hqp
  have hcol : ∀ r : Fin (n + 1),
      (mMatrix B (basisVec (R := R) q) p)[r][Fin.last n] =
        if r = r_q then (1 : R) else (0 : R) := by
    intro r
    rw [mMatrix_entry_last]
    rw [basisVec_getElem]
    by_cases hreq : r = r_q
    · subst hreq
      rw [if_pos rfl]
      have : skipIndex p r_q = q :=
        skipIndex_at_q_eq_q_of_gt p q hqp
      rw [this]
      exact if_pos rfl
    · rw [if_neg hreq]
      have hne : skipIndex p r ≠ q := by
        intro heq
        have hq_eq : skipIndex p r_q = q :=
          skipIndex_at_q_eq_q_of_gt p q hqp
        have : skipIndex p r = skipIndex p r_q := heq.trans hq_eq.symm
        exact hreq (skipIndex_injective p this)
      exact if_neg hne
  rw [det_eq_signed_minor_of_col_basis (mMatrix B (basisVec (R := R) q) p) r_q
        (Fin.last n) hcol]
  congr 1
  unfold nDet
  exact congrArg det
    (deleteRowCol_mMatrix_at_q_eq_nMatrix_of_gt B
      (basisVec (R := R) q) p q hqp)

/-- Basis-vector evaluation of `mDet` when `q > p`: the basis vector
`e_q` becomes the standard basis vector `e_{q.val - 1}` in the last
column of `mMatrix B (basisVec q) p`, so Laplace along that column
recovers a signed `n × n` minor of `B`. -/
theorem mDet_basisVec_eq_signed_nDet_of_lt
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (p q : Fin (n + 2)) (hpq : p.val < q.val) :
    mDet B (basisVec (R := R) q) p =
      cofactorSign (R := R)
        (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 1)) (Fin.last n) *
      nDet B p q hpq := by
  unfold mDet
  -- Last column of `mMatrix B (basisVec q) p` is e_{r_q} where r_q = q.val - 1.
  let r_q : Fin (n + 1) := ⟨q.val - 1, by have := q.isLt; omega⟩
  show (mMatrix B (basisVec (R := R) q) p).det =
      cofactorSign (R := R) r_q (Fin.last n) * nDet B p q hpq
  have hcol : ∀ r : Fin (n + 1),
      (mMatrix B (basisVec (R := R) q) p)[r][Fin.last n] =
        if r = r_q then (1 : R) else (0 : R) := by
    intro r
    rw [mMatrix_entry_last]
    rw [basisVec_getElem]
    by_cases hreq : r = r_q
    · subst hreq
      rw [if_pos rfl]
      have : skipIndex p r_q = q :=
        skipIndex_at_q_minus_one_eq_q_of_lt p q hpq
      rw [this]
      exact if_pos rfl
    · rw [if_neg hreq]
      -- Need: (if skipIndex p r = q then 1 else 0) = 0, i.e., skipIndex p r ≠ q.
      have hne : skipIndex p r ≠ q := by
        intro heq
        -- skipIndex p is injective, and skipIndex p r_q = q.
        have hq_eq : skipIndex p r_q = q :=
          skipIndex_at_q_minus_one_eq_q_of_lt p q hpq
        have : skipIndex p r = skipIndex p r_q := heq.trans hq_eq.symm
        exact hreq (skipIndex_injective p this)
      exact if_neg hne
  rw [det_eq_signed_minor_of_col_basis (mMatrix B (basisVec (R := R) q) p) r_q
        (Fin.last n) hcol]
  congr 1
  unfold nDet
  exact congrArg det
    (deleteRowCol_mMatrix_at_q_minus_one_eq_nMatrix_of_lt B
      (basisVec (R := R) q) p q hpq)

/-- `mDet B (basisVec p) p = 0`: the basis vector `e_p` becomes the zero
column inside `mMatrix B (basisVec p) p` after row `p` is deleted, so
the determinant vanishes. -/
theorem mDet_basisVec_eq_zero_of_eq {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (B : Matrix R (n + 2) n) (p : Fin (n + 2)) :
    mDet B (basisVec (R := R) p) p = 0 := by
  unfold mDet
  -- The last column of `mMatrix B (basisVec p) p` is identically zero.
  have hcol : (fun r : Fin (n + 1) =>
      (basisVec (R := R) p)[skipIndex p r]) = (fun _ => (0 : R)) := by
    funext r
    rw [basisVec_getElem]
    exact if_neg (skipIndex_ne p r)
  -- Express mMatrix as colReplace with that zero function on the last column.
  rw [mMatrix_eq_colReplace_last B (basisVec (R := R) p)
        (basisVec (R := R) p) p]
  rw [hcol]
  exact det_colReplace_zero _ _

/-- Ordered basis-pair evaluation for `twoColDet`: if `a < b`, the only
surviving ordered pair is the deleted-row pair `(a, b)`. -/
theorem twoColDet_basisVec_basisVec_of_lt
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (a b : Fin (n + 2)) (hab : a.val < b.val) :
    twoColDet B (basisVec (R := R) a) (basisVec (R := R) b) =
      cofactorSign (R := R) b (Fin.last (n + 1)) *
        (cofactorSign (R := R)
          (⟨a.val, by have := b.isLt; omega⟩ : Fin (n + 1)) (Fin.last n) *
          nDet B a b hab) := by
  rw [twoColDet_eq_sum_mDet]
  rw [foldl_basisVec_weighted_single (R := R) b
      (fun p => cofactorSign (R := R) p (Fin.last (n + 1)) *
        mDet B (basisVec (R := R) a) p)]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B b a hab]

/-- Reverse ordered basis-pair evaluation for `twoColDet`: if `b < a`,
the determinant recovers the same deleted-row pair with the reversed
coefficient order. -/
theorem twoColDet_basisVec_basisVec_of_gt
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (a b : Fin (n + 2)) (hba : b.val < a.val) :
    twoColDet B (basisVec (R := R) a) (basisVec (R := R) b) =
      cofactorSign (R := R) b (Fin.last (n + 1)) *
        (cofactorSign (R := R)
          (⟨a.val - 1, by have := a.isLt; omega⟩ : Fin (n + 1)) (Fin.last n) *
          nDet B b a hba) := by
  rw [twoColDet_eq_sum_mDet]
  rw [foldl_basisVec_weighted_single (R := R) b
      (fun p => cofactorSign (R := R) p (Fin.last (n + 1)) *
        mDet B (basisVec (R := R) a) p)]
  rw [mDet_basisVec_eq_signed_nDet_of_lt B b a hba]

/-- A repeated basis vector in the two appended columns makes
`twoColDet` vanish. -/
theorem twoColDet_basisVec_basisVec_of_eq
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (a : Fin (n + 2)) :
    twoColDet B (basisVec (R := R) a) (basisVec (R := R) a) = 0 := by
  rw [twoColDet_eq_sum_mDet]
  rw [foldl_basisVec_weighted_single (R := R) a
      (fun p => cofactorSign (R := R) p (Fin.last (n + 1)) *
        mDet B (basisVec (R := R) a) p)]
  rw [mDet_basisVec_eq_zero_of_eq B a]
  grind

/-- Evaluation of `twoColDet` when the final appended column is a basis
vector. This is the one-column Laplace expansion with the remaining
`mDet` minor exposed directly. -/
theorem twoColDet_basisVec_right
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (u : Vector R (n + 2)) (b : Fin (n + 2)) :
    twoColDet B u (basisVec (R := R) b) =
      cofactorSign (R := R) b (Fin.last (n + 1)) * mDet B u b := by
  rw [twoColDet_eq_sum_mDet]
  rw [foldl_basisVec_weighted_single (R := R) b
      (fun p => cofactorSign (R := R) p (Fin.last (n + 1)) * mDet B u p)]

/-- Bilinear basis expansion of `twoColDet` over the two appended columns.
The basis-pair terms are reduced by
`twoColDet_basisVec_basisVec_of_lt`,
`twoColDet_basisVec_basisVec_of_gt`, and
`twoColDet_basisVec_basisVec_of_eq`. -/
theorem twoColDet_eq_sum_basisVec_pairs
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (u v : Vector R (n + 2)) :
    twoColDet B u v =
      (List.finRange (n + 2)).foldl
        (fun acc b =>
          acc + v[b] *
            (List.finRange (n + 2)).foldl
              (fun acc a =>
                acc + u[a] * twoColDet B (basisVec (R := R) a)
                  (basisVec (R := R) b)) 0) 0 := by
  rw [twoColDet_eq_sum_mDet]
  apply foldl_acc_congr
  intro acc b _hmem
  rw [mDet_eq_sum_basisVec B u b]
  congr 2
  calc
    cofactorSign (R := R) b (Fin.last (n + 1)) *
        (List.finRange (n + 2)).foldl
          (fun acc a => acc + u[a] * mDet B (basisVec (R := R) a) b) 0 =
      (List.finRange (n + 2)).foldl
        (fun acc a =>
          acc + cofactorSign (R := R) b (Fin.last (n + 1)) *
            (u[a] * mDet B (basisVec (R := R) a) b)) 0 := by
        rw [foldl_det_sum_mul_left_zero]
    _ =
      (List.finRange (n + 2)).foldl
        (fun acc a =>
          acc + u[a] * twoColDet B (basisVec (R := R) a)
            (basisVec (R := R) b)) 0 := by
        apply foldl_det_sum_congr
        intro a _ha
        rw [twoColDet_basisVec_right B (basisVec (R := R) a) b]
        grind

private theorem cofactorSign_consecutive_last_neg
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (a : Nat) (ha : a + 1 < n + 1) :
    cofactorSign (R := R) (⟨a + 1, ha⟩ : Fin (n + 1)) (Fin.last n) =
      -cofactorSign (R := R) (⟨a, by omega⟩ : Fin (n + 1)) (Fin.last n) := by
  unfold cofactorSign
  simp only [Fin.val_mk, Fin.last]
  by_cases h : (a + n) % 2 = 0
  · have hnext : (a + 1 + n) % 2 ≠ 0 := by omega
    rw [if_pos h, if_neg hnext]
  · have hnext : (a + 1 + n) % 2 = 0 := by omega
    rw [if_neg h, if_pos hnext]
    grind

private theorem det_plucker_three_term_basisVec_of_eq_p1
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (p1 p2 p3 : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    mDet B (basisVec (R := R) p1) p1 * nDet B p2 p3 h23 -
      mDet B (basisVec (R := R) p1) p2 *
        nDet B p1 p3 (Nat.lt_trans h12 h23) +
      mDet B (basisVec (R := R) p1) p3 * nDet B p1 p2 h12 = 0 := by
  rw [mDet_basisVec_eq_zero_of_eq B p1]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p2 p1 h12]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p3 p1 (Nat.lt_trans h12 h23)]
  grind

private theorem det_plucker_three_term_basisVec_of_eq_p2
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (p1 p2 p3 : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    mDet B (basisVec (R := R) p2) p1 * nDet B p2 p3 h23 -
      mDet B (basisVec (R := R) p2) p2 *
        nDet B p1 p3 (Nat.lt_trans h12 h23) +
      mDet B (basisVec (R := R) p2) p3 * nDet B p1 p2 h12 = 0 := by
  rw [mDet_basisVec_eq_signed_nDet_of_lt B p1 p2 h12]
  rw [mDet_basisVec_eq_zero_of_eq B p2]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p3 p2 h23]
  have hp2pos : 0 < p2.val := by omega
  have hrow :
      (⟨p2.val, by have := p3.isLt; omega⟩ : Fin (n + 1)) =
        (⟨p2.val - 1 + 1, by have := p3.isLt; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp
    omega
  rw [hrow]
  rw [cofactorSign_consecutive_last_neg (R := R) (p2.val - 1)
      (by have := p3.isLt; omega)]
  grind

private theorem det_plucker_three_term_basisVec_of_eq_p3
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (p1 p2 p3 : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    mDet B (basisVec (R := R) p3) p1 * nDet B p2 p3 h23 -
      mDet B (basisVec (R := R) p3) p2 *
        nDet B p1 p3 (Nat.lt_trans h12 h23) +
      mDet B (basisVec (R := R) p3) p3 * nDet B p1 p2 h12 = 0 := by
  rw [mDet_basisVec_eq_signed_nDet_of_lt B p1 p3 (Nat.lt_trans h12 h23)]
  rw [mDet_basisVec_eq_signed_nDet_of_lt B p2 p3 h23]
  rw [mDet_basisVec_eq_zero_of_eq B p3]
  grind

private theorem det_plucker_three_term_of_basisVec
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n) (v : Vector R (n + 2))
    (p1 p2 p3 : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (hbasis : ∀ q : Fin (n + 2),
      mDet B (basisVec (R := R) q) p1 * nDet B p2 p3 h23 -
        mDet B (basisVec (R := R) q) p2 *
          nDet B p1 p3 (Nat.lt_trans h12 h23) +
        mDet B (basisVec (R := R) q) p3 * nDet B p1 p2 h12 = 0) :
    mDet B v p1 * nDet B p2 p3 h23 -
      mDet B v p2 * nDet B p1 p3 (Nat.lt_trans h12 h23) +
      mDet B v p3 * nDet B p1 p2 h12 = 0 := by
  rw [mDet_eq_sum_basisVec B v p1]
  rw [mDet_eq_sum_basisVec B v p2]
  rw [mDet_eq_sum_basisVec B v p3]
  rw [← foldl_det_sum_mul_right_zero (List.finRange (n + 2))
      (fun q => v[q] * mDet B (basisVec (R := R) q) p1)
      (nDet B p2 p3 h23)]
  rw [← foldl_det_sum_mul_right_zero (List.finRange (n + 2))
      (fun q => v[q] * mDet B (basisVec (R := R) q) p2)
      (nDet B p1 p3 (Nat.lt_trans h12 h23))]
  rw [← foldl_det_sum_mul_right_zero (List.finRange (n + 2))
      (fun q => v[q] * mDet B (basisVec (R := R) q) p3)
      (nDet B p1 p2 h12)]
  apply foldl_det_sum_sub_add_zero
      (List.finRange (n + 2))
      (fun q => v[q] * mDet B (basisVec (R := R) q) p1 *
        nDet B p2 p3 h23)
      (fun q => v[q] * mDet B (basisVec (R := R) q) p2 *
        nDet B p1 p3 (Nat.lt_trans h12 h23))
      (fun q => v[q] * mDet B (basisVec (R := R) q) p3 *
        nDet B p1 p2 h12)
  · grind
  · intro q _hq
    have hq := hbasis q
    grind

/-! ### Two-row replacement determinant Plucker kernel

The square-matrix two-row determinant Plucker identity: replacing distinct
rows `a` and `b` of an `(n+1) × (n+1)` matrix `M` by vectors `u` and `v` is
controlled by the cofactor-row pairings of `u` and `v` against the original
cofactors of rows `a` and `b`. The proof routes through the single-column
adjugate identity, computed by expanding the `(c, s)` entry of
`adjugate (setRow M r u) * (setRow M r u * adjugate M)` in two ways. -/

/-- Entry formula for matrix multiplication: the `(i, j)` entry of `A * B`
is the `foldl`-sum of `A[i][l] * B[l][j]` over `l`. -/
private theorem mul_apply_foldl
    {R : Type u} [Lean.Grind.CommRing R] {n m k : Nat}
    (A : Matrix R n m) (B : Matrix R m k) (i : Fin n) (j : Fin k) :
    (A * B)[i][j] =
      (List.finRange m).foldl
        (fun acc l => acc + A[i][l] * B[l][j]) 0 := by
  change (Matrix.mul A B)[i][j] = _
  unfold Matrix.mul
  rw [getElem_ofFn]
  unfold Matrix.dot Hex.Vector.dotProduct
  apply foldl_acc_congr
  intro acc l _hmem
  rw [row_getElem, col_getElem]

/-- Row decomposition of `setRow M r u * adjugate M`: the `(i, s)` entry is
the `cofactor-row pairing` of `M`'s row `s` against the (possibly replaced)
row of `setRow M r u` at position `i`. -/
private theorem setRow_mul_adjugate_apply_row
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (r : Fin (n + 1)) (u : Vector R (n + 1))
    (i s : Fin (n + 1)) :
    (setRow M r u * adjugate M)[i][s] =
      cofactorRowPairing M s ((setRow M r u)[i]) := by
  rw [mul_apply_foldl]
  unfold cofactorRowPairing
  apply foldl_acc_congr
  intro acc l _hmem
  rw [adjugate_get]

/-- The replaced row contributes the cofactor-row pairing of `u` against the
`s`-row cofactors of the original matrix. -/
private theorem setRow_mul_adjugate_apply_self
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (r : Fin (n + 1)) (u : Vector R (n + 1))
    (s : Fin (n + 1)) :
    (setRow M r u * adjugate M)[r][s] = cofactorRowPairing M s u := by
  rw [setRow_mul_adjugate_apply_row, setRow_get_self]

/-- Non-replaced rows of `setRow M r u * adjugate M` reproduce the
`M * adjugate M` structure: `det M` on the diagonal, zero off-diagonal. -/
private theorem setRow_mul_adjugate_apply_ne
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (r : Fin (n + 1)) (u : Vector R (n + 1))
    (i s : Fin (n + 1)) (hir : i ≠ r) :
    (setRow M r u * adjugate M)[i][s] = if i = s then det M else 0 := by
  rw [setRow_mul_adjugate_apply_row, setRow_row_ne M r i u hir]
  by_cases his : i = s
  · subst his
    rw [if_pos rfl]
    exact cofactorRowPairing_self M i
  · rw [if_neg his]
    exact cofactorRowPairing_alien_eq_zero M i s his

/-- Lift a bilinear "`det · f = a · g - b · h`" pointwise identity over a
`foldl`-pairing against an arbitrary row weighting. This is the generic
column-summation lemma used to assemble the two-row Plucker identity from
the single-column adjugate identity. -/
private theorem foldl_pairing_mul_sub
    {R : Type u} [Lean.Grind.CommRing R] {β : Type v} (xs : List β)
    (det a b accF accG accH : R) (row f g h : β → R)
    (hacc : det * accF = a * accG - b * accH)
    (hpoint : ∀ x, det * f x = a * g x - b * h x) :
    det * xs.foldl (fun acc x => acc + row x * f x) accF =
      a * xs.foldl (fun acc x => acc + row x * g x) accG -
        b * xs.foldl (fun acc x => acc + row x * h x) accH := by
  induction xs generalizing accF accG accH with
  | nil => simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      have hx := hpoint x
      calc
        det * (accF + row x * f x) =
            det * accF + row x * (det * f x) := by grind
        _ = a * (accG + row x * g x) - b * (accH + row x * h x) := by
            rw [hacc, hx]; grind

/-- Single-column adjugate identity for a one-row replacement.

For matrix `M`, distinct rows `r` and `s`, replacement row `u`, and column
`c`, the determinant of `M` paired with the row-replaced cofactor at `(s, c)`
decomposes as a bilinear difference of cofactor-row pairings against the
original cofactors at rows `s` and `r`.

The proof computes the `(c, s)` entry of
`adjugate (setRow M r u) * (setRow M r u * adjugate M)` two ways: directly,
by isolating the `i = r` and `i = s` terms, and via `mul_assoc` plus
`adjugate_mul_apply`. -/
private theorem det_mul_cofactor_setRow_eq
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1))
    (r s c : Fin (n + 1)) (u : Vector R (n + 1)) (hrs : s ≠ r) :
    det M * cofactor (setRow M r u) s c =
      cofactorRowPairing M r u * cofactor M s c -
        cofactorRowPairing M s u * cofactor M r c := by
  -- Way 1: by `mul_assoc`, the `(c, s)` entry of
  -- `adjugate (setRow M r u) * (setRow M r u * adjugate M)` equals the entry of
  -- `(adjugate (setRow M r u) * setRow M r u) * adjugate M`. Then
  -- `adjugate_mul_apply` reduces the inner factor to `if c = l then det
  -- (setRow M r u) else 0`, and the remaining `foldl` extracts the `l = c` term.
  have hway1 :
      (adjugate (setRow M r u) * (setRow M r u * adjugate M))[c][s] =
        det (setRow M r u) * cofactor M s c := by
    rw [show adjugate (setRow M r u) * (setRow M r u * adjugate M) =
            (adjugate (setRow M r u) * setRow M r u) * adjugate M
            from (Hex.Matrix.mul_assoc (adjugate (setRow M r u)) (setRow M r u)
              (adjugate M)).symm]
    rw [mul_apply_foldl (adjugate (setRow M r u) * setRow M r u) (adjugate M) c s]
    have hcongr :
        (List.finRange (n + 1)).foldl
            (fun acc l =>
              acc + (adjugate (setRow M r u) * setRow M r u)[c][l] *
                (adjugate M)[l][s]) 0 =
          (List.finRange (n + 1)).foldl
            (fun acc l =>
              acc + if l = c then
                det (setRow M r u) * cofactor M s l else 0) 0 := by
      apply foldl_acc_congr
      intro acc l _hmem
      congr 1
      rw [adjugate_mul_apply, adjugate_get]
      by_cases hcl : c = l
      · subst hcl
        rw [if_pos rfl, if_pos rfl]
      · have hlc : l ≠ c := fun h => hcl h.symm
        rw [if_neg hcl, if_neg hlc]
        grind
    rw [hcongr]
    have hmatch :=
      foldl_add_with_unique_match (α := R) (List.finRange (n + 1)) (0 : R) c
        (fun l => det (setRow M r u) * cofactor M s l)
        (List.mem_finRange c) (List.nodup_finRange (n + 1))
    rw [hmatch]
    grind
  -- Way 2: compute the same entry by unfolding the matrix product into a sum
  -- over `i`. Decompose the body via `setRow_mul_adjugate_apply_self` / `_ne`
  -- into two single-extract terms.
  have hway2 :
      (adjugate (setRow M r u) * (setRow M r u * adjugate M))[c][s] =
        cofactor M r c * cofactorRowPairing M s u +
          det M * cofactor (setRow M r u) s c := by
    rw [mul_apply_foldl (adjugate (setRow M r u)) (setRow M r u * adjugate M) c s]
    have hbody :
        (List.finRange (n + 1)).foldl
            (fun acc i =>
              acc + (adjugate (setRow M r u))[c][i] *
                (setRow M r u * adjugate M)[i][s]) 0 =
          (List.finRange (n + 1)).foldl
            (fun acc i =>
              acc +
                ((if i = r then
                    (adjugate (setRow M r u))[c][i] *
                      cofactorRowPairing M s u
                  else 0) +
                 (if i = s then
                    (adjugate (setRow M r u))[c][i] * det M
                  else 0))) 0 := by
      apply foldl_acc_congr
      intro acc i _hmem
      congr 1
      by_cases hir : i = r
      · subst hir
        have his_ne : i ≠ s := fun h => hrs h.symm
        rw [setRow_mul_adjugate_apply_self M i u s, if_pos rfl, if_neg his_ne,
          Lean.Grind.AddCommMonoid.add_zero]
      · rw [setRow_mul_adjugate_apply_ne M r u i s hir, if_neg hir]
        by_cases his : i = s
        · subst his
          rw [if_pos rfl, if_pos rfl, Lean.Grind.AddCommMonoid.zero_add]
        · rw [if_neg his, if_neg his, Lean.Grind.Semiring.mul_zero,
            Lean.Grind.AddCommMonoid.add_zero]
    rw [hbody]
    rw [foldl_det_sum_add_zero]
    have hr_extract :=
      foldl_add_with_unique_match (α := R) (List.finRange (n + 1)) (0 : R) r
        (fun i => (adjugate (setRow M r u))[c][i] * cofactorRowPairing M s u)
        (List.mem_finRange r) (List.nodup_finRange (n + 1))
    have hs_extract :=
      foldl_add_with_unique_match (α := R) (List.finRange (n + 1)) (0 : R) s
        (fun i => (adjugate (setRow M r u))[c][i] * det M)
        (List.mem_finRange s) (List.nodup_finRange (n + 1))
    rw [hr_extract, hs_extract]
    -- Beta-reduce the extracted lambdas.
    show (0 : R) +
        (adjugate (setRow M r u))[c][r] * cofactorRowPairing M s u +
        ((0 : R) + (adjugate (setRow M r u))[c][s] * det M) =
        cofactor M r c * cofactorRowPairing M s u +
          det M * cofactor (setRow M r u) s c
    rw [adjugate_get (setRow M r u) c r, adjugate_get (setRow M r u) c s]
    have hcof_r : cofactor (setRow M r u) r c = cofactor M r c := by
      unfold cofactor
      rw [deleteRowCol_setRow_self M r c u]
    rw [hcof_r]
    rw [Lean.Grind.AddCommMonoid.zero_add, Lean.Grind.AddCommMonoid.zero_add,
        Lean.Grind.CommSemiring.mul_comm (cofactor (setRow M r u) s c) (det M)]
  -- Combine: hway1 = hway2 gives the desired identity after rearranging.
  have hcombined :
      det (setRow M r u) * cofactor M s c =
        cofactor M r c * cofactorRowPairing M s u +
          det M * cofactor (setRow M r u) s c :=
    hway1.symm.trans hway2
  rw [det_setRow_eq_cofactorRowPairing M r u] at hcombined
  -- Rearrange `hcombined` to extract `det M * cofactor (setRow M r u) s c`.
  -- From `Y = Z + X` derive `X = Y - Z`, where the subtracted term carries the
  -- expected `cofactorRowPairing M s u * cofactor M r c` ordering via mul_comm.
  rw [Lean.Grind.CommSemiring.mul_comm (cofactor M r c)
        (cofactorRowPairing M s u)] at hcombined
  -- hcombined: cofactorRowPairing M r u * cofactor M s c =
  --   cofactorRowPairing M s u * cofactor M r c + det M * cofactor (setRow M r u) s c
  rw [show
      cofactorRowPairing M r u * cofactor M s c -
        cofactorRowPairing M s u * cofactor M r c =
      det M * cofactor (setRow M r u) s c from ?_]
  rw [hcombined]
  rw [Lean.Grind.AddCommMonoid.add_comm (cofactorRowPairing M s u * cofactor M r c)
        (det M * cofactor (setRow M r u) s c)]
  exact Lean.Grind.AddCommGroup.add_sub_cancel

/-- Two-row replacement determinant Plucker kernel.

For matrix `M : Matrix R (n+1) (n+1)`, distinct rows `a` and `b`, and
replacement vectors `u`, `v`, the determinant of `M` paired with the
two-row-replaced cofactor-row pairing satisfies the quadratic Sylvester
relation against the four one-row cofactor-row pairings of `u` and `v`. -/
theorem cofactorRowPairing_setRow_plucker
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (a b : Fin (n + 1)) (hab : a ≠ b)
    (u v : Vector R (n + 1)) :
    det M * cofactorRowPairing (setRow M a u) b v =
      cofactorRowPairing M a u * cofactorRowPairing M b v -
        cofactorRowPairing M a v * cofactorRowPairing M b u := by
  -- The natural shape from `foldl_pairing_mul_sub` has `cofactorRowPairing M
  -- b u * cofactorRowPairing M a v` for the subtracted product; commute to the
  -- issue's stated form via `mul_comm` afterwards.
  have hpre :
      det M * cofactorRowPairing (setRow M a u) b v =
        cofactorRowPairing M a u * cofactorRowPairing M b v -
          cofactorRowPairing M b u * cofactorRowPairing M a v := by
    unfold cofactorRowPairing
    apply foldl_pairing_mul_sub
    · grind
    · intro c
      exact det_mul_cofactor_setRow_eq M a b c u
        (fun h => hab h.symm)
  rw [hpre]
  grind

/-- Two-row replacement determinant Plucker identity. -/
theorem det_setRow_setRow_mul_det
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (a b : Fin (n + 1)) (hab : a ≠ b)
    (u v : Vector R (n + 1)) :
    det M * det (setRow (setRow M a u) b v) =
      det (setRow M a u) * det (setRow M b v) -
        det (setRow M a v) * det (setRow M b u) := by
  rw [det_setRow_eq_cofactorRowPairing (setRow M a u) b v,
    det_setRow_eq_cofactorRowPairing M a u,
    det_setRow_eq_cofactorRowPairing M b v,
    det_setRow_eq_cofactorRowPairing M a v,
    det_setRow_eq_cofactorRowPairing M b u]
  exact cofactorRowPairing_setRow_plucker M a b hab u v

/-- Canonical ordered four-row Grassmann-Plucker identity for the raw `nDet`
minors of an `(n + 2) × n` matrix: for any four strictly increasing rows
`r0 < r1 < r2 < r3`, the three pairings of `nDet` two-row minors sum to zero
with the canonical Plucker signs.

The proof applies the square two-row replacement Plucker kernel
`det_setRow_setRow_mul_det` to `nMatrix B r0 r1 h01` at the two replacement
positions `s2 = ⟨r2.val - 2, _⟩` and `s3 = ⟨r3.val - 2, _⟩`, then transports
each of the five resulting determinants to a signed `nDet` minor via the
single-row and double-row `setRow ∘ setRow` row-replacement transports. The
sign exponents collapse against the common factor
`(-1) ^ ((r2 - r0 - 2) + (r3 - r1 - 2))`. -/
private theorem nDet_plucker_four_row_canonical
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (r0 r1 r2 r3 : Fin (n + 2))
    (h01 : r0.val < r1.val) (h12 : r1.val < r2.val)
    (h23 : r2.val < r3.val) :
    nDet B r2 r3 h23 * nDet B r0 r1 h01 -
      nDet B r1 r3 (Nat.lt_trans h12 h23) *
        nDet B r0 r2 (Nat.lt_trans h01 h12) +
      nDet B r1 r2 h12 *
        nDet B r0 r3 (Nat.lt_trans h01 (Nat.lt_trans h12 h23)) = 0 := by
  -- A strictly increasing four-tuple in `Fin (n + 2)` forces `n ≥ 2`. Reduce
  -- to `n = n' + 1` so the `(n+1) × (n+1)` square Plucker kernel applies to
  -- `nMatrix B r0 r1 h01`.
  cases n with
  | zero =>
      have := r3.isLt
      omega
  | succ n' =>
      have hsk2 : r2.val - 2 < n' + 1 := by have := r3.isLt; omega
      have hsk3 : r3.val - 2 < n' + 1 := by have := r3.isLt; omega
      have hs2s3 :
          (⟨r2.val - 2, hsk2⟩ : Fin (n' + 1)) ≠ ⟨r3.val - 2, hsk3⟩ := by
        intro heq
        have : r2.val - 2 = r3.val - 2 := congrArg Fin.val heq
        omega
      have hsq :=
        det_setRow_setRow_mul_det (nMatrix B r0 r1 h01)
          (⟨r2.val - 2, hsk2⟩ : Fin (n' + 1))
          (⟨r3.val - 2, hsk3⟩ : Fin (n' + 1)) hs2s3 B[r0] B[r1]
      have ho :=
        det_setRow_setRow_nMatrix_r2_r0_r3_r1
          B r0 r1 r2 r3 h01 h12 h23
      have ha :=
        det_setRow_nMatrix_r2_r0
          B r0 r1 r2 r3 h01 h12 h23
      have hb :=
        det_setRow_nMatrix_r3_r1
          B r0 r1 r2 r3 h01 h12 h23
      have hc :=
        det_setRow_nMatrix_r2_r1
          B r0 r1 r2 r3 h01 h12 h23
      have hd :=
        det_setRow_nMatrix_r3_r0
          B r0 r1 r2 r3 h01 h12 h23
      simp only at ho ha hb hc hd
      rw [ho, ha, hb, hc, hd] at hsq
      change nDet B r0 r1 h01 * _ = _ at hsq
      -- Sign-cancellation facts: square cancellation of the common factor,
      -- the `pow_add` split of the outer exponent, the `pow_succ` shift for
      -- `r3 - r1 - 1`, and the parity identity
      -- `(r2 - r1 - 1) + (r3 - r0 - 2) = ((r2 - r0 - 2) + (r3 - r1 - 2)) + 1`
      -- that aligns the two off-diagonal sign products.
      have hself :=
        neg_one_pow_mul_self (R := R)
          ((r2.val - r0.val - 2) + (r3.val - r1.val - 2))
      have hpow_ab :=
        Lean.Grind.Semiring.pow_add (-1 : R)
          (r2.val - r0.val - 2) (r3.val - r1.val - 2)
      have hpow_b1 :
          (-1 : R) ^ (r3.val - r1.val - 1) =
            (-1 : R) ^ (r3.val - r1.val - 2) * (-1 : R) := by
        have heq : r3.val - r1.val - 1 = (r3.val - r1.val - 2) + 1 := by omega
        rw [heq, Lean.Grind.Semiring.pow_succ]
      have hpow_de :
          (-1 : R) ^ (r2.val - r1.val - 1) * (-1 : R) ^ (r3.val - r0.val - 2) =
            (-1 : R) ^ ((r2.val - r0.val - 2) + (r3.val - r1.val - 2)) *
              (-1 : R) := by
        rw [← Lean.Grind.Semiring.pow_add]
        have heq :
            (r2.val - r1.val - 1) + (r3.val - r0.val - 2) =
              ((r2.val - r0.val - 2) + (r3.val - r1.val - 2)) + 1 := by omega
        rw [heq, Lean.Grind.Semiring.pow_succ]
      grind

/-- Raw `nDet` three-term Plucker identity for the q-between case
`p1 < q < p2 < p3`: a direct specialization of the canonical four-row
identity at `(r0, r1, r2, r3) = (p1, q, p2, p3)`. The product order of the
two off-diagonal pairs is swapped relative to the canonical statement;
multiplication in a `CommRing` discharges the swap. -/
private theorem det_plucker_three_term_nDet_of_between_p1_p2
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (p1 q p2 p3 : Fin (n + 2))
    (h1q : p1.val < q.val) (hq2 : q.val < p2.val) (h23 : p2.val < p3.val) :
    nDet B p2 p3 h23 * nDet B p1 q h1q -
      nDet B p1 p2 (Nat.lt_trans h1q hq2) *
        nDet B q p3 (Nat.lt_trans hq2 h23) +
      nDet B p1 p3 (Nat.lt_trans h1q (Nat.lt_trans hq2 h23)) *
        nDet B q p2 hq2 = 0 := by
  have hraw := nDet_plucker_four_row_canonical B p1 q p2 p3 h1q hq2 h23
  grind

/-- Raw `nDet` three-term Grassmann-Plucker identity for the q-before case
`q < p1 < p2 < p3`: the canonical ordered four-row identity
`nDet_plucker_four_row_canonical` instantiated at `(r0, r1, r2, r3) := (q, p1, p2, p3)`.
This is the q-before kernel consumed by the downstream consecutive-top Gram
pattern. -/
private theorem det_plucker_three_term_nDet_of_lt_p1
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (q p1 p2 p3 : Fin (n + 2))
    (hq1 : q.val < p1.val) (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    nDet B p2 p3 h23 * nDet B q p1 hq1 -
      nDet B p1 p3 (Nat.lt_trans h12 h23) *
        nDet B q p2 (Nat.lt_trans hq1 h12) +
      nDet B p1 p2 h12 *
        nDet B q p3 (Nat.lt_trans hq1 (Nat.lt_trans h12 h23)) = 0 :=
  nDet_plucker_four_row_canonical B q p1 p2 p3 hq1 h12 h23

/-- Basis-vector case `q < p1` of the three-term Plucker identity:
expanding `mDet B (basisVec q) p_i` via `mDet_basisVec_eq_signed_nDet_of_gt`
(each `q < p_i`) reduces the goal to the raw q-before `nDet` kernel. -/
private theorem det_plucker_three_term_basisVec_of_lt_p1_of_nDet
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (q p1 p2 p3 : Fin (n + 2))
    (hq1 : q.val < p1.val) (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    mDet B (basisVec (R := R) q) p1 * nDet B p2 p3 h23 -
      mDet B (basisVec (R := R) q) p2 *
        nDet B p1 p3 (Nat.lt_trans h12 h23) +
      mDet B (basisVec (R := R) q) p3 * nDet B p1 p2 h12 = 0 := by
  have hraw := det_plucker_three_term_nDet_of_lt_p1 B q p1 p2 p3 hq1 h12 h23
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p1 q hq1]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p2 q (Nat.lt_trans hq1 h12)]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p3 q
      (Nat.lt_trans hq1 (Nat.lt_trans h12 h23))]
  grind

/-- Basis-vector case `p1 < q < p2` of the three-term Plucker identity.
The first expansion uses `mDet_basisVec_eq_signed_nDet_of_lt`; the latter two
use `mDet_basisVec_eq_signed_nDet_of_gt`. The consecutive cofactor signs differ
by a minus sign, leaving the raw q-between `nDet` kernel. -/
private theorem det_plucker_three_term_basisVec_of_between_p1_p2_of_nDet
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (B : Matrix R (n + 2) n)
    (p1 q p2 p3 : Fin (n + 2))
    (h1q : p1.val < q.val) (hq2 : q.val < p2.val) (h23 : p2.val < p3.val) :
    mDet B (basisVec (R := R) q) p1 * nDet B p2 p3 h23 -
      mDet B (basisVec (R := R) q) p2 *
        nDet B p1 p3 (Nat.lt_trans (Nat.lt_trans h1q hq2) h23) +
      mDet B (basisVec (R := R) q) p3 *
        nDet B p1 p2 (Nat.lt_trans h1q hq2) = 0 := by
  have hraw :=
    det_plucker_three_term_nDet_of_between_p1_p2 B p1 q p2 p3 h1q hq2 h23
  rw [mDet_basisVec_eq_signed_nDet_of_lt B p1 q h1q]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p2 q hq2]
  rw [mDet_basisVec_eq_signed_nDet_of_gt B p3 q (Nat.lt_trans hq2 h23)]
  have hrow :
      (⟨q.val, by have := p3.isLt; omega⟩ : Fin (n + 1)) =
        (⟨q.val - 1 + 1, by have := p3.isLt; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp
    omega
  rw [hrow]
  rw [cofactorSign_consecutive_last_neg (R := R) (q.val - 1)
      (by have := p3.isLt; omega)]
  grind

/-- Consecutive-top vector-column Plücker identity.

This is the Mathlib-free specialization used by the Gram/Bareiss trajectory:
the three distinguished rows are `alpha`, `k`, and `k+1` inside
`Fin (k + 2)`, so the top row is the last possible row and there is no
`q > p3` basis-vector case. -/
theorem det_plucker_three_term_consecutive_top
    {R : Type u} [Lean.Grind.CommRing R] {k : Nat}
    (B : Matrix R (k + 2) k) (v : Vector R (k + 2))
    (alpha : Fin (k + 2)) (halpha : alpha.val < k) :
    let pk : Fin (k + 2) := ⟨k, by omega⟩
    let plast : Fin (k + 2) := Fin.last (k + 1)
    mDet B v alpha * nDet B pk plast (by dsimp [pk, plast]; omega) -
      mDet B v pk * nDet B alpha plast (by dsimp [plast]; omega) +
      mDet B v plast * nDet B alpha pk (by dsimp [pk]; exact halpha) = 0 := by
  let pk : Fin (k + 2) := ⟨k, by omega⟩
  let plast : Fin (k + 2) := Fin.last (k + 1)
  have h12 : alpha.val < pk.val := by
    dsimp [pk]
    exact halpha
  have h23 : pk.val < plast.val := by
    dsimp [pk, plast]
    omega
  dsimp only
  refine det_plucker_three_term_of_basisVec B v alpha pk plast h12 h23 ?_
  intro q
  by_cases hq_alpha : q = alpha
  · subst q
    exact det_plucker_three_term_basisVec_of_eq_p1 B alpha pk plast h12 h23
  by_cases hq_pk : q = pk
  · subst hq_pk
    exact det_plucker_three_term_basisVec_of_eq_p2 B alpha pk plast h12 h23
  by_cases hq_plast : q = plast
  · subst hq_plast
    exact det_plucker_three_term_basisVec_of_eq_p3 B alpha pk plast h12 h23
  by_cases hq_lt_alpha : q.val < alpha.val
  · exact det_plucker_three_term_basisVec_of_lt_p1_of_nDet
      B q alpha pk plast hq_lt_alpha h12 h23
  have halpha_lt_q : alpha.val < q.val := by
    omega
  have hq_lt_pk : q.val < pk.val := by
    have hq_ne_pk_val : q.val ≠ k := by
      intro hv
      apply hq_pk
      apply Fin.ext
      dsimp [pk]
      exact hv
    have hq_ne_plast_val : q.val ≠ k + 1 := by
      intro hv
      apply hq_plast
      apply Fin.ext
      dsimp [plast]
      exact hv
    have hq_bound : q.val < k + 2 := q.isLt
    dsimp [pk]
    omega
  exact det_plucker_three_term_basisVec_of_between_p1_p2_of_nDet
    B alpha q pk plast halpha_lt_q hq_lt_pk h23


end Matrix
end Hex
