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

/-- Deleting the destination row of `setRow M dst v` gives the same minor
as deleting the destination row of `M`: the replaced row is removed
anyway, so the new entries are invisible. -/
theorem deleteRowCol_setRow_self {R : Type u} {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (dst col : Fin (n + 1))
    (v : Vector R (n + 1)) :
    deleteRowCol (setRow M dst v) dst col = deleteRowCol M dst col := by
  ext i hi j hj
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
  have hmul :
      (M * adjugate M)[i][j] =
        Hex.Vector.dotProduct (row M i) (col (adjugate M) j) := by
    change (Matrix.mul M (adjugate M))[i][j] = _
    unfold Matrix.mul
    show
      (ofFn fun i j => Hex.Vector.dotProduct (row M i) (col (adjugate M) j))[i][j] =
        _
    simp [ofFn]
  have hentry :
      (M * adjugate M)[i][j] =
        (List.finRange (n + 1)).foldl
          (fun acc k => acc + M[i][k] * cofactor M j k) 0 := by
    rw [hmul]
    unfold Hex.Vector.dotProduct
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
      unfold Hex.Vector.dotProduct
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
      unfold Hex.Vector.dotProduct
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
  ext r hr c hc
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
  ext r hr c hc
  let rr : Fin n := ⟨r, hr⟩
  let cc : Fin n := ⟨c, hc⟩
  show (M * N)[rr][cc] = (columnSumMatrix M N.transpose)[rr][cc]
  rw [columnSumMatrix_entry]
  change (Matrix.mul M N)[rr][cc] = _
  unfold Matrix.mul ofFn
  rw [vector_ofFn_getElem_fin, vector_ofFn_getElem_fin]
  unfold Hex.Vector.dotProduct
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

/-- Foldl over a list whose body is identically zero leaves the seed
unchanged. -/
theorem foldl_add_zero_body {α : Type u} [Lean.Grind.CommRing α]
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
theorem foldl_add_with_unique_match {α : Type u}
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
  unfold Hex.Vector.dotProduct
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


end Matrix
end Hex
