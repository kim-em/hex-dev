module

public import HexMatrix.Determinant.Permutation
import all HexMatrix.Determinant.Permutation

public section

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- Replace one column of a square matrix by the supplied column function. -/
@[expose]
def colReplace {R : Type u} {n : Nat} (M : Matrix R n n) (dst : Fin n)
    (v : Fin n → R) : Matrix R n n :=
  Matrix.ofFn fun r c => if c = dst then v r else M[r][c]

/-- Entrywise characterization of `colReplace`: the destination column is
read from the replacement function and every other column is read from `M`. -/
theorem colReplace_get {R : Type u} {n : Nat} (M : Matrix R n n) (dst r c : Fin n)
    (v : Fin n → R) :
    (colReplace M dst v)[r][c] = if c = dst then v r else M[r][c] := by
  simp [colReplace, Matrix.ofFn]

/-- The per-permutation product `detProduct` is additive in the replaced
column: splitting that column's entries as `v + w` splits the product as a sum. -/
private theorem detProduct_colReplace_add {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct (colReplace M dst (fun r => v r + w r)) perm =
      detProduct (colReplace M dst v) perm +
        detProduct (colReplace M dst w) perm := by
  let pivot : Fin n := ⟨perm.toList.idxOf dst,
    by
      simpa [Vector.length_toList] using
        fin_idxOf_lt dst (by simp [Vector.length_toList]) hnodup⟩
  have hpivot : perm[pivot] = dst := by
    have hlt : perm.toList.idxOf dst < perm.toList.length :=
      fin_idxOf_lt dst (by simp [Vector.length_toList]) hnodup
    have hget : perm.toList[perm.toList.idxOf dst]'hlt = dst :=
      List.getElem_idxOf (x := dst) (xs := perm.toList) hlt
    change perm.toList[pivot.val]'(by simp [Vector.length_toList, pivot.isLt]) = dst
    simp [pivot] at hget ⊢
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc i => acc * (colReplace M dst (fun r => v r + w r))[i][perm[i]]) 1 =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            (colReplace M dst v)[x][perm[x]] + (colReplace M dst w)[x][perm[x]]
          else
            (colReplace M dst v)[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        rw [colReplace_get, colReplace_get, colReplace_get]
        by_cases hxp : x = pivot
        · subst x
          rw [if_pos hpivot, if_pos hpivot, if_pos hpivot, if_pos rfl]
        · rw [if_neg hxp]
          have hperm_ne : perm[x] ≠ dst := by
            intro hperm
            have hxidx : perm.toList.idxOf perm[x] = x.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
            have hpidx : perm.toList.idxOf dst = pivot.val := rfl
            have hval : x.val = pivot.val := by
              rw [← hxidx, hperm, hpidx]
            exact hxp (Fin.ext hval)
          change (if perm[x] = dst then v x + w x else M[x][perm[x]]) =
            (if perm[x] = dst then v x else M[x][perm[x]])
          rw [if_neg hperm_ne, if_neg hperm_ne]
    _ =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            (colReplace M dst v)[x][perm[x]] + (1 : R) * (colReplace M dst w)[x][perm[x]]
          else
            (colReplace M dst v)[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        by_cases hxp : x = pivot
        · rw [if_pos hxp]
          grind
        · simp [hxp]
    _ =
      (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst v)[x][perm[x]]) 1 +
        (1 : R) * (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst w)[x][perm[x]]) 1 := by
        exact
          foldl_det_product_single_add (R := R) (β := Fin n)
            (List.finRange n) pivot (1 : R)
            (fun x => (colReplace M dst v)[x][perm[x]])
            (fun x => (colReplace M dst w)[x][perm[x]])
            1 (List.mem_finRange pivot) (List.nodup_finRange n)
            (by
              intro x _hx hxp
              have hperm_ne : perm[x] ≠ dst := by
                intro hperm
                have hxidx : perm.toList.idxOf perm[x] = x.val := by
                  simpa [Vector.getElem_toList, Vector.length_toList] using
                    hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
                have hpidx : perm.toList.idxOf dst = pivot.val := rfl
                have hval : x.val = pivot.val := by
                  rw [← hxidx, hperm, hpidx]
                exact hxp (Fin.ext hval)
              change (colReplace M dst w)[x][perm[x]] =
                (colReplace M dst v)[x][perm[x]]
              rw [colReplace_get, colReplace_get]
              change (if perm[x] = dst then w x else M[x][perm[x]]) =
                (if perm[x] = dst then v x else M[x][perm[x]])
              rw [if_neg hperm_ne, if_neg hperm_ne])
    _ =
      (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst v)[x][perm[x]]) 1 +
        (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst w)[x][perm[x]]) 1 := by
        grind

/-- The per-permutation product `detProduct` is homogeneous in the replaced
column: scaling that column's entries by `c` scales the product by `c`. -/
private theorem detProduct_colReplace_smul {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct (colReplace M dst (fun r => c * v r)) perm =
      c * detProduct (colReplace M dst v) perm := by
  let pivot : Fin n := ⟨perm.toList.idxOf dst,
    by
      simpa [Vector.length_toList] using
        fin_idxOf_lt dst (by simp [Vector.length_toList]) hnodup⟩
  have hpivot : perm[pivot] = dst := by
    have hlt : perm.toList.idxOf dst < perm.toList.length :=
      fin_idxOf_lt dst (by simp [Vector.length_toList]) hnodup
    have hget : perm.toList[perm.toList.idxOf dst]'hlt = dst :=
      List.getElem_idxOf (x := dst) (xs := perm.toList) hlt
    change perm.toList[pivot.val]'(by simp [Vector.length_toList, pivot.isLt]) = dst
    simp [pivot] at hget ⊢
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc i => acc * (colReplace M dst (fun r => c * v r))[i][perm[i]]) 1 =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            c * (colReplace M dst v)[x][perm[x]]
          else
            (colReplace M dst v)[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        rw [colReplace_get, colReplace_get]
        by_cases hxp : x = pivot
        · subst x
          rw [if_pos hpivot, if_pos hpivot, if_pos rfl]
        · rw [if_neg hxp]
          have hperm_ne : perm[x] ≠ dst := by
            intro hperm
            have hxidx : perm.toList.idxOf perm[x] = x.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
            have hpidx : perm.toList.idxOf dst = pivot.val := rfl
            have hval : x.val = pivot.val := by
              rw [← hxidx, hperm, hpidx]
            exact hxp (Fin.ext hval)
          change (if perm[x] = dst then c * v x else M[x][perm[x]]) =
            (if perm[x] = dst then v x else M[x][perm[x]])
          rw [if_neg hperm_ne, if_neg hperm_ne]
    _ =
      c * (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst v)[x][perm[x]]) 1 := by
        exact
          foldl_det_product_single_scale (R := R) (β := Fin n)
            (List.finRange n) pivot c
            (fun x => (colReplace M dst v)[x][perm[x]])
            1 (List.mem_finRange pivot) (List.nodup_finRange n)

/-- The signed Leibniz term `detTerm` is additive in the replaced column:
splitting that column's entries as `v + w` splits the term as a sum. -/
private theorem detTerm_colReplace_add {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (colReplace M dst (fun r => v r + w r)) perm =
      detTerm (colReplace M dst v) perm + detTerm (colReplace M dst w) perm := by
  unfold detTerm
  rw [detProduct_colReplace_add M dst v w perm hnodup]
  grind

/-- The signed Leibniz term `detTerm` is homogeneous in the replaced column:
scaling that column's entries by `c` scales the term by `c`. -/
private theorem detTerm_colReplace_smul {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (colReplace M dst (fun r => c * v r)) perm =
      c * detTerm (colReplace M dst v) perm := by
  unfold detTerm
  rw [detProduct_colReplace_smul M dst c v perm hnodup]
  grind

/-- Determinant linearity in one replaced column, additive form. -/
theorem det_colReplace_add {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R) :
    det (colReplace M dst (fun r => v r + w r)) =
      det (colReplace M dst v) + det (colReplace M dst w) := by
  simp [det]
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (colReplace M dst (fun r => v r + w r)) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm =>
          acc + (detTerm (colReplace M dst v) perm +
            detTerm (colReplace M dst w) perm)) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        exact detTerm_colReplace_add M dst v w perm (permutationVectors_nodup hmem)
    _ =
      (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (colReplace M dst v) perm) 0 +
        (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (colReplace M dst w) perm) 0 := by
        exact foldl_det_sum_add_zero
          (permutationVectors n)
          (detTerm (colReplace M dst v))
          (detTerm (colReplace M dst w))

/-- Determinant linearity in one replaced column, scalar form. -/
theorem det_colReplace_smul {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R) :
    det (colReplace M dst (fun r => c * v r)) =
      c * det (colReplace M dst v) := by
  simp [det]
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (colReplace M dst (fun r => c * v r)) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + c * detTerm (colReplace M dst v) perm) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        exact detTerm_colReplace_smul M dst c v perm (permutationVectors_nodup hmem)
    _ =
      c * (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (colReplace M dst v) perm) 0 := by
        exact foldl_det_sum_mul_left_zero
          (permutationVectors n) c (detTerm (colReplace M dst v))

/-- The assembled determinant `det` vanishes when the replaced column is zero. -/
private theorem det_colReplace_zero {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) :
    det (colReplace M dst (fun _ => (0 : R))) = 0 := by
  have h := det_colReplace_smul M dst (0 : R) (fun _ => (1 : R))
  have hcol : (fun r : Fin n => (0 : R) * (1 : R)) = fun _ => (0 : R) := by
    funext r
    grind
  rw [hcol] at h
  grind

/-- Replacing a column by itself leaves the matrix unchanged. -/
theorem colReplace_self {R : Type u} {n : Nat}
    (M : Matrix R n n) (dst : Fin n) :
    colReplace M dst (fun r => M[r][dst]) = M := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change (colReplace M dst (fun r => M[r][dst]))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
    M[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [colReplace_get]
  by_cases hc' : (⟨c, hc⟩ : Fin n) = dst
  · rw [if_pos hc']
    exact congrArg (fun c' : Fin n => M[(⟨r, hr⟩ : Fin n)][c']) hc'.symm
  · rw [if_neg hc']

/-- Determinant linearity in one replaced column, finite-list form. -/
theorem det_colReplace_sum_list {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) {β : Type v} (xs : List β)
    (coeff : β → R) (source : β → Fin n → R) :
    det (colReplace M dst
        (fun r => xs.foldl (fun acc x => acc + coeff x * source x r) 0)) =
      xs.foldl
        (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 := by
  induction xs with
  | nil =>
      exact det_colReplace_zero M dst
  | cons x xs ih =>
      simp only [List.foldl_cons]
      let tail : Fin n → R :=
        fun r => xs.foldl (fun acc x => acc + coeff x * source x r) 0
      have hcol :
          (fun r : Fin n =>
              xs.foldl (fun acc x => acc + coeff x * source x r)
                (0 + coeff x * source x r)) =
            fun r => coeff x * source x r + tail r := by
        funext r
        rw [foldl_det_sum_start]
        simp [tail]
        grind
      calc
        det (colReplace M dst
            (fun r => xs.foldl (fun acc x => acc + coeff x * source x r)
              (0 + coeff x * source x r))) =
          det (colReplace M dst (fun r => coeff x * source x r + tail r)) := by
            rw [hcol]
        _ =
          det (colReplace M dst (fun r => coeff x * source x r)) +
            det (colReplace M dst tail) := by
            exact det_colReplace_add M dst (fun r => coeff x * source x r) tail
        _ =
          coeff x * det (colReplace M dst (source x)) +
            xs.foldl (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 := by
            rw [det_colReplace_smul]
            simp [tail]
            rw [ih]
        _ =
          xs.foldl (fun acc x => acc + coeff x * det (colReplace M dst (source x)))
            (0 + coeff x * det (colReplace M dst (source x))) := by
            have hstart :=
              (foldl_det_sum_start (R := R) xs
                (fun x => coeff x * det (colReplace M dst (source x)))
                (0 + coeff x * det (colReplace M dst (source x)))).symm
            calc
              coeff x * det (colReplace M dst (source x)) +
                  xs.foldl
                    (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 =
                (0 + coeff x * det (colReplace M dst (source x))) +
                  xs.foldl
                    (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 := by
                  grind
              _ =
                xs.foldl
                  (fun acc x => acc + coeff x * det (colReplace M dst (source x)))
                  (0 + coeff x * det (colReplace M dst (source x))) := hstart

/-- Determinant linearity in one replaced column, indexed by `Fin m`. -/
theorem det_colReplace_sum_finRange {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (M : Matrix R n n) (dst : Fin n) (coeff : Fin m → R)
    (source : Fin m → Fin n → R) :
    det (colReplace M dst
        (fun r => (List.finRange m).foldl
          (fun acc x => acc + coeff x * source x r) 0)) =
      (List.finRange m).foldl
        (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 :=
  det_colReplace_sum_list M dst (List.finRange m) coeff source

/-- Square matrix whose `j`-th column is the finite linear combination of the
columns of `source` with coefficients from row `j` of `coeff`. -/
@[expose]
def columnSumMatrix {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) : Matrix R n n :=
  ofFn fun r j =>
    (List.finRange m).foldl (fun acc k => acc + coeff[j][k] * source[r][k]) 0

@[grind =] private theorem columnSumMatrix_entry
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (r j : Fin n) :
    (columnSumMatrix source coeff)[r][j] =
      (List.finRange m).foldl (fun acc k => acc + coeff[j][k] * source[r][k]) 0 := by
  simp [columnSumMatrix, ofFn]

private theorem colReplace_columnSumMatrix_self
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (dst : Fin n) :
    colReplace (columnSumMatrix source coeff) dst
        (fun r => (List.finRange m).foldl
          (fun acc k => acc + coeff[dst][k] * source[r][k]) 0) =
      columnSumMatrix source coeff := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change
    (colReplace (columnSumMatrix source coeff) dst
        (fun r => (List.finRange m).foldl
          (fun acc k => acc + coeff[dst][k] * source[r][k]) 0))[
          (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix source coeff)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [colReplace_get]
  by_cases hcol : (⟨c, hc⟩ : Fin n) = dst
  · subst dst
    rw [if_pos rfl]
    exact (columnSumMatrix_entry source coeff (⟨r, hr⟩ : Fin n) (⟨c, hc⟩ : Fin n)).symm
  · simp [hcol]

private theorem det_columnSumMatrix_expand_column
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (dst : Fin n) :
    det (columnSumMatrix source coeff) =
      (List.finRange m).foldl
        (fun acc k =>
          acc + coeff[dst][k] *
            det (colReplace (columnSumMatrix source coeff) dst (fun r => source[r][k]))) 0 := by
  have hsum :=
    det_colReplace_sum_list
    (columnSumMatrix source coeff) dst (List.finRange m)
    (fun k => coeff[dst][k]) (fun k r => source[r][k])
  have hself := colReplace_columnSumMatrix_self source coeff dst
  rw [hself] at hsum
  exact hsum

/-- Matrix obtained during the ordered column expansion: columns with
`choices c = some k` have already been specialized to source column `k`, while
unassigned columns remain the finite coefficient-weighted column sum. -/
private def columnChoiceMatrix {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (choices : Fin n → Option (Fin m)) : Matrix R n n :=
  ofFn fun r c =>
    match choices c with
    | some k => source[r][k]
    | none => (List.finRange m).foldl (fun acc k => acc + coeff[c][k] * source[r][k]) 0

@[grind =] private theorem columnChoiceMatrix_entry
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (choices : Fin n → Option (Fin m)) (r c : Fin n) :
    (columnChoiceMatrix source coeff choices)[r][c] =
      match choices c with
      | some k => source[r][k]
      | none => (List.finRange m).foldl (fun acc k => acc + coeff[c][k] * source[r][k]) 0 := by
  simp [columnChoiceMatrix, ofFn]

/-- A determinant with two equal rows is zero. -/
theorem det_eq_zero_of_row_eq {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hrow : M[src] = M[dst]) :
    det M = 0 := by
  have hdup : rowAddDuplicate M src dst = M := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro c hc
    change (rowAddDuplicate M src dst)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      M[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
    rw [rowAddDuplicate_get]
    by_cases hdst : (⟨r, hr⟩ : Fin n) = dst
    · subst hdst
      simpa using congrArg (fun row => row[(⟨c, hc⟩ : Fin n)]) hrow
    · simp [hdst]
  have hsum := permutationVectors_duplicateRow_sum M src dst h
  rw [hdup] at hsum
  simpa [det] using hsum

/-- A determinant with two equal columns is zero. -/
theorem det_eq_zero_of_col_eq {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst]) :
    det M = 0 := by
  simpa [det] using permutationVectors_duplicateCol_sum M src dst h hcol

/-- Replacing a column by an already-present different column creates a
duplicate column, so the determinant is zero. -/
theorem det_colReplace_existing_col_eq_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst src : Fin n) (hsrcdst : src ≠ dst) :
    det (colReplace M dst (fun r => M[r][src])) = 0 := by
  apply det_eq_zero_of_col_eq (colReplace M dst (fun r => M[r][src])) src dst hsrcdst
  intro r
  rw [colReplace_get, colReplace_get]
  rw [if_neg hsrcdst, if_pos rfl]

/-- Adding a finite linear combination of other columns of `M` to column `dst`
preserves the determinant. The sources are given as a list and each source is
required to differ from `dst`. -/
theorem det_colReplace_add_otherCols {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (sources : List (Fin n)) (coeff : Fin n → R)
    (hsrc : ∀ s ∈ sources, s ≠ dst) :
    det (colReplace M dst
        (fun r => M[r][dst] +
          sources.foldl (fun acc s => acc + coeff s * M[r][s]) 0)) = det M := by
  rw [det_colReplace_add M dst (fun r => M[r][dst])
    (fun r => sources.foldl (fun acc s => acc + coeff s * M[r][s]) 0)]
  rw [colReplace_self M dst]
  have hcomb : det (colReplace M dst
        (fun r => sources.foldl (fun acc s => acc + coeff s * M[r][s]) 0)) = 0 := by
    rw [det_colReplace_sum_list M dst sources coeff (fun s r => M[r][s])]
    -- Show each summand is zero; we use the fact that the foldl over sources
    -- yields zero because each replaced det is zero.
    have hzero_each : ∀ s ∈ sources, coeff s * det (colReplace M dst (fun r => M[r][s])) = 0 := by
      intro s hs
      have hne : s ≠ dst := hsrc s hs
      rw [det_colReplace_existing_col_eq_zero M dst s hne]
      grind
    -- Foldl of a sum that is always zero adds nothing.
    have hfoldl : sources.foldl
        (fun acc s => acc + coeff s * det (colReplace M dst (fun r => M[r][s]))) 0 = 0 := by
      clear hzero_each
      induction sources with
      | nil => rfl
      | cons s ss ih =>
          simp only [List.foldl_cons]
          have hs : coeff s * det (colReplace M dst (fun r => M[r][s])) = 0 := by
            have hne : s ≠ dst := hsrc s (by simp)
            rw [det_colReplace_existing_col_eq_zero M dst s hne]
            grind
          rw [hs]
          have hsrc' : ∀ s' ∈ ss, s' ≠ dst := fun s' hs' => hsrc s' (by simp [hs'])
          have hzero_acc : (0 : R) + 0 = 0 := by grind
          rw [hzero_acc]
          exact ih hsrc'
    exact hfoldl
  rw [hcomb]
  grind

/-- Square submatrix obtained by selecting an ordered tuple of columns. -/
@[expose]
def columnTupleMatrix {R : Type u} {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m) : Matrix R n n :=
  ofFn fun r c => A[r][cols c]

/-- Entry `(r, c)` of the column-selected minor is the source entry
`A[r][cols c]`. -/
@[grind =] theorem columnTupleMatrix_entry {R : Type u} {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m) (r c : Fin n) :
    (columnTupleMatrix A cols)[r][c] = A[r][cols c] := by
  simp [columnTupleMatrix, ofFn]

/-- Interpret an ordered column tuple vector as its column-selection function. -/
@[expose]
def columnTupleVectorFn {n m : Nat} (cols : Vector (Fin m) n) : Fin n → Fin m :=
  fun i => cols[i]

/-- Applying the column-selection function at `i` reads the `i`-th entry
`cols[i]` of the tuple vector. -/
@[simp, grind =] theorem columnTupleVectorFn_apply {n m : Nat}
    (cols : Vector (Fin m) n) (i : Fin n) :
    columnTupleVectorFn cols i = cols[i] := rfl

/-- Reindexing the selected columns by a permutation is entrywise the generic
column permutation of the selected minor.

Unattributed: the LHS `[r][c]` is not in simp-normal form (`Fin.getElem_fin`
rewrites the `Fin` indices to `↑r`/`↑c`), and `grind =` rejects the pattern
because the columns `s sigma` appear only under the `fun i => s[sigma[i]]`
binder, so the LHS cannot instantiate them. Invoked explicitly via `rw`. -/
theorem columnTupleMatrix_compose_perm_entry
    {R : Type u} {n m : Nat} (A : Matrix R n m)
    (s : Vector (Fin m) n) (sigma : Vector (Fin n) n)
    (r c : Fin n) :
    (columnTupleMatrix A (fun i => s[sigma[i]]))[r][c] =
      (columnTupleMatrix A (columnTupleVectorFn s))[r][sigma[c]] := by
  rw [columnTupleMatrix_entry, columnTupleMatrix_entry]
  exact (congrArg (fun col : Fin m => A[r][col])
    (columnTupleVectorFn_apply s (sigma[c]))).symm

/-- Reindexing the selected columns by a permutation is the generic column
permutation of the selected minor. -/
theorem columnTupleMatrix_compose_perm_eq_colPermute
    {R : Type u} {n m : Nat} (A : Matrix R n m)
    (s : Vector (Fin m) n) (sigma : Vector (Fin n) n) :
    columnTupleMatrix A (fun i => s[sigma[i]]) =
      (ofFn fun r c => (columnTupleMatrix A (columnTupleVectorFn s))[r][sigma[c]]) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change
    (columnTupleMatrix A (fun i => s[sigma[i]]))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (ofFn fun r c =>
        (columnTupleMatrix A (columnTupleVectorFn s))[r][sigma[c]])[
          (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnTupleMatrix_compose_perm_entry]
  simp [Matrix.ofFn]

/-- Specialization of the generic column-permutation determinant sign theorem
to selected-minor matrices. -/
theorem det_columnTupleMatrix_compose_perm
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (s : Vector (Fin m) n) (sigma : Vector (Fin n) n)
    (hsigma : sigma ∈ permutationVectors n) :
    det (columnTupleMatrix A (fun i => s[sigma[i]])) =
      detSign (R := R) sigma * det (columnTupleMatrix A (columnTupleVectorFn s)) := by
  rw [columnTupleMatrix_compose_perm_eq_colPermute A s sigma]
  exact det_colPermute_vector (columnTupleMatrix A (columnTupleVectorFn s)) sigma hsigma

/-- Enumerate all ordered `n`-tuples of columns from `Fin m`. -/
@[expose]
def columnTupleVectors : (n m : Nat) → List (Vector (Fin m) n)
  | 0, _ => [emptyVec]
  | n + 1, m =>
      (columnTupleVectors n m).flatMap fun pref =>
        (List.finRange m).map fun c =>
          insertAt c pref (Fin.last n)

private theorem columnTupleVectors_ofFn_succ
    {n m : Nat} (cols : Fin (n + 1) → Fin m) :
    Vector.ofFn cols =
      insertAt (cols (Fin.last n)) (Vector.ofFn fun i : Fin n => cols i.castSucc)
        (Fin.last n) := by
  apply Vector.ext
  intro i hi
  change (Vector.ofFn cols)[(⟨i, hi⟩ : Fin (n + 1))] =
    (insertAt (cols (Fin.last n)) (Vector.ofFn fun i : Fin n => cols i.castSucc)
      (Fin.last n))[(⟨i, hi⟩ : Fin (n + 1))]
  by_cases hlast : i = n
  · subst i
    simp [insertAt, List.getElem_insertIdx_self]
    exact congrArg cols (Fin.ext rfl)
  · have hi_lt : i < n := by omega
    simp [insertAt, List.getElem_insertIdx_of_lt, hi_lt]

/-- Every ordered column-selection function occurs in `columnTupleVectors`. -/
theorem columnTupleVectors_mem_ofFn {n m : Nat} (cols : Fin n → Fin m) :
    Vector.ofFn cols ∈ columnTupleVectors n m := by
  induction n with
  | zero =>
      simp [columnTupleVectors, emptyVec]
  | succ n ih =>
      rw [columnTupleVectors_ofFn_succ cols]
      rw [columnTupleVectors, List.mem_flatMap]
      refine ⟨Vector.ofFn fun i : Fin n => cols i.castSucc, ih (fun i => cols i.castSucc), ?_⟩
      rw [List.mem_map]
      exact ⟨cols (Fin.last n), List.mem_finRange (cols (Fin.last n)), rfl⟩

private theorem insertAt_last_injective_pair {α : Type u} {n : Nat}
    {c c' : α} {pref pref' : Vector α n}
    (h : insertAt c pref (Fin.last n) = insertAt c' pref' (Fin.last n)) :
    c = c' ∧ pref = pref' := by
  constructor
  · have hlast :
        (insertAt c pref (Fin.last n))[Fin.last n] =
          (insertAt c' pref' (Fin.last n))[Fin.last n] := by
      rw [h]
    rw [insertAt_get_self, insertAt_get_self] at hlast
    exact hlast
  · apply Vector.ext
    intro i hi
    let idx : Fin n := ⟨i, hi⟩
    have hidx :
        (insertAt c pref (Fin.last n))[idx.castSucc] =
          (insertAt c' pref' (Fin.last n))[idx.castSucc] := by
      rw [h]
    rw [insertAt_last_get_castSucc, insertAt_last_get_castSucc] at hidx
    exact hidx

private theorem columnTupleVectors_flatMap_last_nodup {n m : Nat} :
    ∀ (prefs : List (Vector (Fin m) n)), prefs.Nodup →
      (prefs.flatMap fun pref =>
        (List.finRange m).map fun c => insertAt c pref (Fin.last n)).Nodup
  | [], _ => by simp
  | pref :: prefs, hnodup => by
      simp only [List.flatMap_cons]
      simp only [List.nodup_cons] at hnodup
      rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · apply list_nodup_map_on (List.nodup_finRange m)
        intro c _hc c' _hc' h
        exact (insertAt_last_injective_pair h).1
      · exact columnTupleVectors_flatMap_last_nodup prefs hnodup.2
      · intro a hahead b hbsuffix hab
        rcases List.mem_map.mp hahead with ⟨c, _hc, rfl⟩
        rcases List.mem_flatMap.mp hbsuffix with ⟨pref', hpref', hb⟩
        rcases List.mem_map.mp hb with ⟨c', _hc', hb_eq⟩
        have hrec :
            insertAt c pref (Fin.last n) =
              insertAt c' pref' (Fin.last n) := hab.trans hb_eq.symm
        have hpref_eq := (insertAt_last_injective_pair hrec).2
        subst hpref_eq
        exact hnodup.1 hpref'

private theorem columnTupleVectors_nodup {n m : Nat} :
    (columnTupleVectors n m).Nodup := by
  induction n with
  | zero =>
      simp [columnTupleVectors]
  | succ n ih =>
      rw [columnTupleVectors]
      exact columnTupleVectors_flatMap_last_nodup (columnTupleVectors n m) ih

/-- Product coefficient attached to an ordered column tuple in the Gram expansion. -/
@[expose]
def columnTupleCoeff {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (A : Matrix R n m) (cols : Vector (Fin m) n) : R :=
  (List.finRange n).foldl (fun acc i => acc * A[i][cols[i]]) 1

/-- The determinant summand associated to an ordered column tuple. -/
@[expose]
def columnTupleExpansionTerm {R : Type u} [Lean.Grind.Ring R] {n m : Nat}
    (A : Matrix R n m) (cols : Vector (Fin m) n) : R :=
  columnTupleCoeff A cols * det (columnTupleMatrix A (columnTupleVectorFn cols))

/-- An ordered column-tuple minor with a repeated selected column has determinant zero. -/
theorem det_columnTupleMatrix_eq_zero_of_col_eq
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m)
    {src dst : Fin n} (h : src ≠ dst) (hcols : cols src = cols dst) :
    det (columnTupleMatrix A cols) = 0 := by
  apply det_eq_zero_of_col_eq (columnTupleMatrix A cols) src dst h
  intro r
  rw [columnTupleMatrix_entry, columnTupleMatrix_entry]
  exact congrArg (fun c : Fin m => A[r][c]) hcols

/-- An ordered column-tuple minor with a non-injective selected-column map has
determinant zero. -/
theorem det_columnTupleMatrix_eq_zero_of_not_injective
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m)
    (hcols : ¬ Function.Injective cols) :
    det (columnTupleMatrix A cols) = 0 := by
  classical
  have hdup : ∃ src dst : Fin n, cols src = cols dst ∧ src ≠ dst := by
    rw [Function.Injective] at hcols
    rcases Classical.not_forall.mp hcols with ⟨src, hsrc⟩
    rcases Classical.not_forall.mp hsrc with ⟨dst, hdst⟩
    exact ⟨src, dst, (not_imp.mp hdst).1, fun h => (not_imp.mp hdst).2 h⟩
  rcases hdup with ⟨src, dst, hsame, hne⟩
  exact det_columnTupleMatrix_eq_zero_of_col_eq A cols hne hsame

/-! ### All-column ordered tuple expansion

Iterates `det_columnSumMatrix_expand_column` over every column to express
`det (columnSumMatrix source coeff)` as a sum over ordered column tuples.
Uses a list-based "left prefix" partial assignment, with a Fubini-style
sum-swap to align the iteration order with `columnTupleVectors`.
-/

/-- Sum-swap (Fubini) for the standard determinant-style nested folds. -/
theorem foldl_det_sum_swap {R : Type u} [Lean.Grind.CommRing R]
    {β γ : Type v} (xs : List β) (ys : List γ) (f : β → γ → R) :
    xs.foldl (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 =
      ys.foldl (fun acc y => acc + xs.foldl (fun acc' x => acc' + f x y) 0) 0 := by
  induction xs with
  | nil =>
      simp only [List.foldl_nil]
      exact (foldl_det_sum_zero ys 0).symm
  | cons x xs ih =>
      have hLHS :
          (x :: xs).foldl
              (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 =
            ys.foldl (fun acc' y => acc' + f x y) 0 +
              xs.foldl
                (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 := by
        simp only [List.foldl_cons]
        rw [foldl_det_sum_start xs
              (fun x' => ys.foldl (fun acc' y => acc' + f x' y) 0)
              (0 + ys.foldl (fun acc' y => acc' + f x y) 0)]
        grind
      have hRHS :
          ys.foldl
              (fun acc y => acc + (x :: xs).foldl
                (fun acc' x' => acc' + f x' y) 0) 0 =
            ys.foldl (fun acc' y => acc' + f x y) 0 +
              ys.foldl
                (fun acc y => acc + xs.foldl
                  (fun acc' x' => acc' + f x' y) 0) 0 := by
        have hfun :
            (fun (acc : R) y =>
                acc + (x :: xs).foldl (fun acc' x' => acc' + f x' y) 0) =
              (fun (acc : R) y =>
                acc + (f x y + xs.foldl (fun acc' x' => acc' + f x' y) 0)) := by
          funext acc y
          congr 1
          simp only [List.foldl_cons]
          rw [foldl_det_sum_start xs (fun x' => f x' y) (0 + f x y)]
          grind
        rw [hfun]
        exact foldl_det_sum_add_zero ys (fun y => f x y)
          (fun y => xs.foldl (fun acc' x' => acc' + f x' y) 0)
      rw [hLHS, hRHS, ih]

private theorem foldl_det_sum_nested_start {R : Type u} [Lean.Grind.CommRing R]
    {β γ : Type v} (xs : List β) (ys : List γ) (f : β → γ → R) (z : R) :
    xs.foldl (fun acc x => ys.foldl (fun acc' y => acc' + f x y) acc) z =
      z + xs.foldl
        (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 := by
  induction xs generalizing z with
  | nil =>
      simp only [List.foldl_nil]
      grind
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [foldl_det_sum_start ys (fun y => f x y) z]
      rw [ih (z + ys.foldl (fun acc' y => acc' + f x y) 0)]
      rw [foldl_det_sum_start xs
        (fun x => ys.foldl (fun acc' y => acc' + f x y) 0)
        (0 + ys.foldl (fun acc' y => acc' + f x y) 0)]
      grind

private theorem foldl_det_sum_nested_zero {R : Type u} [Lean.Grind.CommRing R]
    {β γ : Type v} (xs : List β) (ys : List γ) (f : β → γ → R) :
    xs.foldl (fun acc x => ys.foldl (fun acc' y => acc' + f x y) acc) 0 =
      xs.foldl
        (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 := by
  exact (foldl_det_sum_nested_start xs ys f (0 : R)).trans (by grind)

/-- Inner sum-over-permutations collapse: for any row `i`, the Leibniz terms whose
permutation sends row `i` to the last column collapse to `M[i][last] * cofactor M i last`. -/
private theorem foldl_detTerm_insertions_eq
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i : Fin (n + 1)) :
    (permutationVectors n).foldl
        (fun acc v => acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) 0 =
      M[i][Fin.last n] * cofactor M i (Fin.last n) := by
  have hsumands : (permutationVectors n).foldl
        (fun acc v => acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) 0 =
      (permutationVectors n).foldl
        (fun acc v => acc + cofactorSign (R := R) i (Fin.last n) *
          (M[i][Fin.last n] * detTerm (deleteRowCol M i (Fin.last n)) v)) 0 := by
    apply foldl_det_sum_congr
    intro v _hmem
    exact detTerm_insertAt_general M v i
  rw [hsumands]
  rw [foldl_det_sum_mul_left_zero (permutationVectors n)
    (cofactorSign (R := R) i (Fin.last n))
    (fun v => M[i][Fin.last n] * detTerm (deleteRowCol M i (Fin.last n)) v)]
  rw [foldl_det_sum_mul_left_zero (permutationVectors n) M[i][Fin.last n]
    (fun v => detTerm (deleteRowCol M i (Fin.last n)) v)]
  show cofactorSign (R := R) i (Fin.last n) *
       (M[i][Fin.last n] * det (deleteRowCol M i (Fin.last n))) = _
  unfold cofactor
  grind

/-- Laplace expansion of the determinant along the final column. -/
theorem det_eq_foldl_laplace_last
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    det M =
      (List.finRange (n + 1)).foldl
        (fun acc row => acc + M[row][Fin.last n] * cofactor M row (Fin.last n)) 0 := by
  unfold det
  rw [show permutationVectors (n + 1) =
      List.flatMap
        (fun v =>
          (List.finRange (n + 1)).map fun i =>
            insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (permutationVectors n) from rfl]
  rw [foldl_det_sum_flatMap]
  have hmap :
      (permutationVectors n).foldl
        (fun acc v =>
          ((List.finRange (n + 1)).map
            (fun i => insertAt (Fin.last n) (v.map Fin.castSucc) i)).foldl
            (fun acc perm => acc + detTerm M perm) acc) 0 =
      (permutationVectors n).foldl
        (fun acc v =>
          (List.finRange (n + 1)).foldl
            (fun acc i =>
              acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) acc) 0 := by
    apply foldl_acc_congr
    intro acc v _hmem
    simp only [List.foldl_map]
  rw [hmap]
  rw [foldl_det_sum_nested_zero (permutationVectors n) (List.finRange (n + 1))
    (fun v i => detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i))]
  rw [foldl_det_sum_swap (permutationVectors n) (List.finRange (n + 1))
    (fun v i => detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i))]
  apply foldl_acc_congr
  intro acc i _hmem
  congr 1
  exact foldl_detTerm_insertions_eq M i

/-- Laplace expansion of the determinant along the final row. -/
theorem det_eq_foldl_laplace_last_row
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    det M =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M[Fin.last n][col] * cofactor M (Fin.last n) col) 0 := by
  calc
    det M = det M.transpose := (det_transpose M).symm
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M.transpose[col][Fin.last n] *
          cofactor M.transpose col (Fin.last n)) 0 := det_eq_foldl_laplace_last M.transpose
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M[Fin.last n][col] * cofactor M (Fin.last n) col) 0 := by
        apply foldl_acc_congr
        intro acc col _hmem
        rw [cofactor_transpose]
        simp [Matrix.transpose, Matrix.col]

/-- Column permutation that preserves the relative order of every column except
`col`, which is moved to the final position. -/
private def moveColumnToLastValues {n : Nat} (col : Fin (n + 1)) :
    Vector (Fin (n + 1)) (n + 1) :=
  insertAt col (Vector.ofFn fun i : Fin n => skipIndex col i) (Fin.last n)

/-- `moveColumnToLastValues_last` states that the moved column `col` lands in the
final position of the permutation, the defining property that sends the cofactor
column to the last column. -/
private theorem moveColumnToLastValues_last {n : Nat} (col : Fin (n + 1)) :
    (moveColumnToLastValues col)[Fin.last n] = col := by
  exact insertAt_get_self col (Vector.ofFn fun i : Fin n => skipIndex col i) (Fin.last n)

/-- `moveColumnToLastValues_castSucc` states that every non-final position
`i.castSucc` of the permutation holds the original columns with `col` skipped over,
preserving the relative order of the surviving columns. -/
private theorem moveColumnToLastValues_castSucc {n : Nat} (col : Fin (n + 1)) (i : Fin n) :
    (moveColumnToLastValues col)[i.castSucc] = skipIndex col i := by
  rw [moveColumnToLastValues]
  simpa using
    insertAt_last_get_castSucc col (Vector.ofFn fun i : Fin n => skipIndex col i) i

/-- `moveColumnToLastValues_nodup` states that the permutation's values are
pairwise distinct, the no-repeat condition needed to certify it as a genuine
permutation of the columns. -/
private theorem moveColumnToLastValues_nodup {n : Nat} (col : Fin (n + 1)) :
    (moveColumnToLastValues col).toList.Nodup := by
  rw [moveColumnToLastValues, insertAt_last_toList]
  rw [vector_toList_eq]
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · apply list_nodup_map_of_injective
    · intro i j h
      exact skipIndex_injective col (by simpa using h)
    · exact List.nodup_finRange n
  · simp
  · intro x hx y hy hxy
    simp only [List.mem_singleton] at hy
    have hxcol : x = col := hxy.trans hy
    rcases List.mem_map.mp hx with ⟨i, _hi, rfl⟩
    exact skipIndex_ne col i (by simpa using hxcol)

/-- `moveColumnToLastValues_mem_permutationVectors` states that the column move is
a member of `permutationVectors (n + 1)`, packaging the nodup proof so the move can
be fed to the determinant column-permutation machinery. -/
private theorem moveColumnToLastValues_mem_permutationVectors {n : Nat}
    (col : Fin (n + 1)) :
    moveColumnToLastValues col ∈ permutationVectors (n + 1) :=
  permutationVectors_complete (moveColumnToLastValues_nodup col)

/-- `skipIndex_eq_raiseFinAbove` states that the two index-shifting functions agree,
letting the column-move list be rewritten in the `raiseFinAbove` form used by the
inversion-count sign computation. -/
private theorem skipIndex_eq_raiseFinAbove {n : Nat} (col : Fin (n + 1)) (i : Fin n) :
    skipIndex col i = raiseFinAbove col i := by
  unfold skipIndex raiseFinAbove
  split <;> rfl

/-- `moveColumnToLastValues_toList` gives the explicit list form of the column move:
the `n` surviving columns in order (via `raiseFinAbove col`) followed by `col`, the
shape consumed by the inversion-count sign lemma. -/
private theorem moveColumnToLastValues_toList {n : Nat} (col : Fin (n + 1)) :
    (moveColumnToLastValues col).toList =
      ((List.finRange n).map (raiseFinAbove col)) ++ [col] := by
  rw [moveColumnToLastValues, insertAt_last_toList]
  rw [vector_toList_eq]
  apply congrArg (fun xs => xs ++ [col])
  apply List.map_congr_left
  intro i _hi
  simpa using skipIndex_eq_raiseFinAbove col i

/-- `detSign_moveColumnToLastValues` evaluates the sign of the column move to
`(-1) ^ (n - col.val)`, the parity contributed by sliding `col` past the `n - col.val`
columns to its right. -/
private theorem detSign_moveColumnToLastValues
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (col : Fin (n + 1)) :
    detSign (R := R) (moveColumnToLastValues col) =
      (-1 : R) ^ (n - col.val) := by
  have hidList :
      (Vector.ofFn fun i : Fin n => i).toList = List.finRange n := by
    rw [vector_toList_eq]
    simp
  calc
    detSign (R := R) (moveColumnToLastValues col) =
        (-1 : R) ^ (n - col.val) *
          detSign (R := R) (Vector.ofFn fun i : Fin n => i) := by
      apply detSign_of_inversionCount_add
      rw [moveColumnToLastValues_toList, hidList]
      rw [inversionCount_map_raiseFinAbove_append_self]
      rw [foldCount_finRange_ge]
    _ = (-1 : R) ^ (n - col.val) := by
      rw [detSign_identity]
      grind

/-- `neg_one_pow_mul_self` states that a sign `(-1) ^ k` squares to one, the
cancellation used to undo the column-move sign factor when transporting the Laplace
expansion back to the original column. -/
private theorem neg_one_pow_mul_self {R : Type u} [Lean.Grind.CommRing R] (k : Nat) :
    (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
  induction k with
  | zero =>
      grind
  | succ k ih =>
      grind

/-- `cofactorSign_col_eq` relates the cofactor sign at column `col` to
the sign at the last column through the `(-1) ^ (n - col.val)` column-move factor, the
parity bookkeeping that turns last-column Laplace expansion into expansion along `col`. -/
private theorem cofactorSign_col_eq
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (row col : Fin (n + 1)) :
    cofactorSign (R := R) row col =
      (-1 : R) ^ (n - col.val) * cofactorSign (R := R) row (Fin.last n) := by
  unfold cofactorSign
  simp only [Fin.val_last]
  have hle : col.val ≤ n := Nat.le_of_lt_succ col.isLt
  have h := detSignParity_add (R := R) (row.val + col.val) (n - col.val)
  have hsum : row.val + col.val + (n - col.val) = row.val + n := by omega
  rw [hsum] at h
  let s : R := (-1 : R) ^ (n - col.val)
  let a : R := if (row.val + col.val) % 2 = 0 then 1 else -1
  let b : R := if (row.val + n) % 2 = 0 then 1 else -1
  have hs : s * s = 1 := neg_one_pow_mul_self (R := R) (n - col.val)
  have hb : b = s * a := by simpa [a, b, s] using h
  calc
    (if (row.val + col.val) % 2 = 0 then (1 : R) else -1) = a := rfl
    _ = s * (s * a) := by
      have hss : s * (s * a) = a := by
        calc
          s * (s * a) = (s * s) * a := by grind
          _ = 1 * a := by rw [hs]
          _ = a := by grind
      exact hss.symm
    _ = s * b := by rw [hb]
    _ = s * (if (row.val + n) % 2 = 0 then (1 : R) else -1) := rfl

/-- Laplace expansion of the determinant along an arbitrary fixed column. -/
theorem det_eq_foldl_laplace_col
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (col : Fin (n + 1)) :
    det M =
      (List.finRange (n + 1)).foldl
        (fun acc row => acc + M[row][col] * cofactor M row col) 0 := by
  let sigma := moveColumnToLastValues col
  let C : Matrix R (n + 1) (n + 1) := ofFn fun r c => M[r][sigma[c]]
  have hsigma : sigma ∈ permutationVectors (n + 1) :=
    moveColumnToLastValues_mem_permutationVectors col
  have hdetC : det C = (-1 : R) ^ (n - col.val) * det M := by
    calc
      det C = detSign (R := R) sigma * det M := by
        exact det_colPermute_vector M sigma hsigma
      _ = (-1 : R) ^ (n - col.val) * det M := by
        rw [detSign_moveColumnToLastValues col]
  have hsign_sq : (-1 : R) ^ (n - col.val) * ((-1 : R) ^ (n - col.val)) = 1 := by
    exact neg_one_pow_mul_self (R := R) (n - col.val)
  calc
    det M = (-1 : R) ^ (n - col.val) * det C := by
      rw [hdetC]
      grind
    _ =
      (-1 : R) ^ (n - col.val) *
        (List.finRange (n + 1)).foldl
          (fun acc row => acc + C[row][Fin.last n] * cofactor C row (Fin.last n)) 0 := by
        rw [det_eq_foldl_laplace_last C]
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc row =>
          acc + (-1 : R) ^ (n - col.val) *
            (C[row][Fin.last n] * cofactor C row (Fin.last n))) 0 := by
        rw [foldl_det_sum_mul_left_zero]
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc row => acc + M[row][col] * cofactor M row col) 0 := by
        apply foldl_acc_congr
        intro acc row _hmem
        congr 1
        unfold cofactor
        have hClast : C[row][Fin.last n] = M[row][col] := by
          rw [show C[row][Fin.last n] = M[row][sigma[Fin.last n]] by
            simp [C, ofFn]]
          exact congrArg (fun c => M[row][c]) (moveColumnToLastValues_last col)
        have hminor : deleteRowCol C row (Fin.last n) = deleteRowCol M row col := by
          apply Vector.ext
          intro i hi
          apply Vector.ext
          intro j hj
          let ii : Fin n := ⟨i, hi⟩
          let jj : Fin n := ⟨j, hj⟩
          change (deleteRowCol C row (Fin.last n))[ii][jj] =
            (deleteRowCol M row col)[ii][jj]
          rw [deleteRowCol_entry, deleteRowCol_entry]
          rw [show C[skipIndex row ii][skipIndex (Fin.last n) jj] =
              C[skipIndex row ii][jj.castSucc] by
            exact congrArg (fun c => C[skipIndex row ii][c]) (skipIndex_last jj)]
          rw [show C[skipIndex row ii][jj.castSucc] =
              M[skipIndex row ii][sigma[jj.castSucc]] by
            simp [C, ofFn]]
          exact congrArg (fun c => M[skipIndex row ii][c])
            (moveColumnToLastValues_castSucc col jj)
        rw [hClast, hminor]
        rw [cofactorSign_col_eq (R := R) row col]
        grind

/-- Laplace expansion of the determinant along an arbitrary fixed row. -/
theorem det_eq_foldl_laplace_row
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row : Fin (n + 1)) :
    det M =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M[row][col] * cofactor M row col) 0 := by
  calc
    det M = det M.transpose := (det_transpose M).symm
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M.transpose[col][row] *
          cofactor M.transpose col row) 0 := det_eq_foldl_laplace_col M.transpose row
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M[row][col] * cofactor M row col) 0 := by
        apply foldl_acc_congr
        intro acc col _hmem
        rw [cofactor_transpose]
        simp [Matrix.transpose, Matrix.col]

/-- The square matrix obtained from `columnSumMatrix source coeff` by replacing
the first `chosen.length` columns with selected `source` columns indexed by
`chosen`. The remaining columns stay in finite-sum form. -/
private def columnSumMatrixWithPrefix
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) : Matrix R n n :=
  ofFn fun r j =>
    if h : j.val < chosen.length then
      source[r][chosen[j.val]'h]
    else
      (List.finRange m).foldl (fun acc k => acc + coeff[j][k] * source[r][k]) 0

@[grind =] private theorem columnSumMatrixWithPrefix_entry
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) (r j : Fin n) :
    (columnSumMatrixWithPrefix source coeff chosen)[r][j] =
      if h : j.val < chosen.length then
        source[r][chosen[j.val]'h]
      else
        (List.finRange m).foldl
          (fun acc k => acc + coeff[j][k] * source[r][k]) 0 := by
  simp [columnSumMatrixWithPrefix, ofFn]

/-! ### Suffix-based partial assignment

We use a SUFFIX-based parametrization (chosen represents right-fixed columns)
to align with the natural recursion of `columnTupleVectors`, which factors out
the LAST element of the suffix. After Fubini sum-swap, the inductive step
reduces to identity matching of the per-term values. -/

/-- Square matrix where the last `chosen.length` columns are fixed to selected
`source` columns indexed by `chosen` (in order), and the remaining left columns
stay in finite-sum form. -/
private def columnSumMatrixWithSuffix
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) : Matrix R n n :=
  ofFn fun r j =>
    if h : n - chosen.length ≤ j.val then
      source[r][chosen[j.val - (n - chosen.length)]'(by
        have : j.val < n := j.isLt; omega)]
    else
      (List.finRange m).foldl (fun acc k => acc + coeff[j][k] * source[r][k]) 0

@[grind =] private theorem columnSumMatrixWithSuffix_entry
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) (r j : Fin n) :
    (columnSumMatrixWithSuffix source coeff chosen)[r][j] =
      if h : n - chosen.length ≤ j.val then
        source[r][chosen[j.val - (n - chosen.length)]'(by
          have : j.val < n := j.isLt; omega)]
      else
        (List.finRange m).foldl
          (fun acc k => acc + coeff[j][k] * source[r][k]) 0 := by
  simp [columnSumMatrixWithSuffix, ofFn]

private theorem columnSumMatrixWithSuffix_nil
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) :
    columnSumMatrixWithSuffix source coeff [] = columnSumMatrix source coeff := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change (columnSumMatrixWithSuffix source coeff [])[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix source coeff)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnSumMatrixWithSuffix_entry, columnSumMatrix_entry]
  rw [dif_neg (show ¬ n - ([] : List (Fin m)).length ≤ c by simp; omega)]

private theorem columnSumMatrixWithSuffix_eq
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hfull : chosen.length = n) :
    columnSumMatrixWithSuffix source coeff chosen =
      columnTupleMatrix source (fun j => chosen[j.val]'(by omega)) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change (columnSumMatrixWithSuffix source coeff chosen)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnTupleMatrix source (fun j => chosen[j.val]'(by omega)))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnSumMatrixWithSuffix_entry, dif_pos (by omega : n - chosen.length ≤ c)]
  simp [columnTupleMatrix, ofFn, hfull]

/-- Replacing the rightmost sum column of the suffix-partial matrix with a fixed
`source` column extends the suffix by prepending that selection. -/
private theorem colReplace_columnSumMatrixWithSuffix_extend
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) (c : Fin m) :
    colReplace (columnSumMatrixWithSuffix source coeff chosen)
        (⟨n - chosen.length - 1, by omega⟩ : Fin n) (fun r => source[r][c]) =
      columnSumMatrixWithSuffix source coeff (c :: chosen) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro k hk2
  change (colReplace (columnSumMatrixWithSuffix source coeff chosen)
      (⟨n - chosen.length - 1, by omega⟩ : Fin n) (fun r => source[r][c]))[
      (⟨r, hr⟩ : Fin n)][(⟨k, hk2⟩ : Fin n)] =
    (columnSumMatrixWithSuffix source coeff (c :: chosen))[
      (⟨r, hr⟩ : Fin n)][(⟨k, hk2⟩ : Fin n)]
  rw [colReplace_get]
  simp only [columnSumMatrixWithSuffix_entry]
  have hccons_len : (c :: chosen).length = chosen.length + 1 := rfl
  by_cases hkd : (⟨k, hk2⟩ : Fin n) = (⟨n - chosen.length - 1, by omega⟩ : Fin n)
  · have hkeq : k = n - chosen.length - 1 := by
      have := congrArg Fin.val hkd; simpa using this
    rw [if_pos hkd]
    rw [dif_pos (show n - (c :: chosen).length ≤ k by rw [hccons_len]; omega)]
    have hsub0 : k - (n - (c :: chosen).length) = 0 := by rw [hccons_len]; omega
    have hgetval : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
        have : k < n := hk2; rw [hccons_len]; omega) = c := by
      have h1 : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
          have : k < n := hk2; rw [hccons_len]; omega) =
        (c :: chosen)[(0 : Nat)]'(by simp) := by
        congr 1
      rw [h1]
      rfl
    exact congrArg (fun x : Fin m => source[(⟨r, hr⟩ : Fin n)][x]) hgetval.symm
  · rw [if_neg hkd]
    have hkne : k ≠ n - chosen.length - 1 := fun h => hkd (Fin.ext h)
    by_cases hkge : n - chosen.length ≤ k
    · rw [dif_pos hkge]
      have hkge' : n - (c :: chosen).length ≤ k := by rw [hccons_len]; omega
      rw [dif_pos hkge']
      have hidx_eq : k - (n - (c :: chosen).length) = (k - (n - chosen.length)) + 1 := by
        rw [hccons_len]; omega
      have hgetval : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
          have : k < n := hk2; rw [hccons_len]; omega) =
        chosen[k - (n - chosen.length)]'(by have : k < n := hk2; omega) := by
        have h1 : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
            have : k < n := hk2; rw [hccons_len]; omega) =
          (c :: chosen)[(k - (n - chosen.length)) + 1]'(by
            have : k < n := hk2; rw [hccons_len]; omega) := by
          congr 1
        rw [h1]
        rfl
      exact congrArg (fun x : Fin m => source[(⟨r, hr⟩ : Fin n)][x]) hgetval.symm
    · rw [dif_neg hkge]
      have hkge' : ¬ n - (c :: chosen).length ≤ k := by rw [hccons_len]; omega
      rw [dif_neg hkge']

/-- One-step expansion of the suffix-partial matrix: peel off the rightmost sum
column as a sum over `Fin m`. -/
private theorem det_columnSumMatrixWithSuffix_expand
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) :
    det (columnSumMatrixWithSuffix source coeff chosen) =
      (List.finRange m).foldl
        (fun acc c => acc + coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
          det (columnSumMatrixWithSuffix source coeff (c :: chosen))) 0 := by
  let dst : Fin n := ⟨n - chosen.length - 1, by omega⟩
  have hself :
      colReplace (columnSumMatrixWithSuffix source coeff chosen) dst
          (fun r => (List.finRange m).foldl
            (fun acc k => acc + coeff[dst][k] * source[r][k]) 0) =
        columnSumMatrixWithSuffix source coeff chosen := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro c hc
    change (colReplace (columnSumMatrixWithSuffix source coeff chosen) dst _)[
        (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrixWithSuffix source coeff chosen)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
    rw [colReplace_get, columnSumMatrixWithSuffix_entry]
    by_cases hcd : (⟨c, hc⟩ : Fin n) = dst
    · rw [if_pos hcd, hcd]
      rw [dif_neg (show ¬ n - chosen.length ≤ dst.val by simp [dst]; omega)]
    · rw [if_neg hcd]
  have hsum := det_colReplace_sum_list
      (columnSumMatrixWithSuffix source coeff chosen) dst
      (List.finRange m) (fun k => coeff[dst][k]) (fun k r => source[r][k])
  rw [hself] at hsum
  rw [hsum]
  apply foldl_det_sum_congr
  intro c _hc
  congr 2
  exact colReplace_columnSumMatrixWithSuffix_extend source coeff chosen hk c

private def assembleColumnsSuffix {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) (hk : chosen.length ≤ n) :
    Vector (Fin m) n :=
  ⟨(pref.toList ++ chosen).toArray, by
    simp [hk]⟩

@[grind =] private theorem assembleColumnsSuffix_left
    {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) (hk : chosen.length ≤ n)
    (i : Fin (n - chosen.length)) :
    (assembleColumnsSuffix chosen pref hk)[
        (⟨i.val, by
          have hi : i.val < n - chosen.length := i.isLt
          omega⟩ : Fin n)] = pref[i] := by
  simp [assembleColumnsSuffix]

@[grind =] private theorem assembleColumnsSuffix_right
    {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) (hk : chosen.length ≤ n)
    (i : Fin chosen.length) :
    (assembleColumnsSuffix chosen pref hk)[
        (⟨n - chosen.length + i.val, by
          have hi : i.val < chosen.length := i.isLt
          omega⟩ : Fin n)] = chosen[i] := by
  unfold assembleColumnsSuffix
  simp [List.getElem_append_right]

private def vectorLengthCast {α : Type u} {n k : Nat} (h : n = k)
    (v : Vector α n) : Vector α k :=
  match v with
  | ⟨xs, hx⟩ => ⟨xs, by simpa [h] using hx⟩

private theorem columnTupleVectors_foldl_vectorLengthCast
    {α : Type u} {m k l : Nat} (h : k = l)
    (f : α → Vector (Fin m) l → α) (init : α) :
    (columnTupleVectors l m).foldl f init =
      (columnTupleVectors k m).foldl
        (fun acc pref => f acc (vectorLengthCast h pref)) init := by
  subst h
  rfl

private theorem assembleColumnsSuffix_insertAt_last
    {n m : Nat} (chosen : List (Fin m)) (c : Fin m)
    (pref : Vector (Fin m) (n - (c :: chosen).length))
    (hk : (c :: chosen).length ≤ n)
    (hlen : (n - (c :: chosen).length) + 1 = n - chosen.length := by
      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
      omega) :
    assembleColumnsSuffix chosen
        (vectorLengthCast hlen
          (insertAt c pref (Fin.last (n - (c :: chosen).length))))
        (by
          have hcons : (c :: chosen).length = chosen.length + 1 := rfl
          omega) =
      assembleColumnsSuffix (c :: chosen) pref hk := by
  apply Vector.toArray_inj.mp
  unfold assembleColumnsSuffix
  simp only [vectorLengthCast, Vector.toList, insertAt]
  have hidx : (Fin.last (n - (c :: chosen).length)).val = pref.toArray.toList.length := by
    simp
  rw [hidx, list_insertIdx_length]
  simp [List.append_assoc]

private theorem det_columnTupleMatrix_assembleColumnsSuffix_insertAt_last
    {R : Type u} [Lean.Grind.Ring R] {n m : Nat} (source : Matrix R n m)
    (chosen : List (Fin m)) (c : Fin m)
    (pref : Vector (Fin m) (n - (c :: chosen).length))
    (hk : (c :: chosen).length ≤ n)
    (hlen : (n - (c :: chosen).length) + 1 = n - chosen.length := by
      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
      omega) :
    det (columnTupleMatrix source
        (columnTupleVectorFn
          (assembleColumnsSuffix chosen
            (vectorLengthCast hlen
              (insertAt c pref (Fin.last (n - (c :: chosen).length))))
            (by
              have hcons : (c :: chosen).length = chosen.length + 1 := rfl
              omega)))) =
      det (columnTupleMatrix source
        (columnTupleVectorFn (assembleColumnsSuffix (c :: chosen) pref hk))) := by
  rw [assembleColumnsSuffix_insertAt_last chosen c pref hk hlen]

private def partialColumnTupleCoeff {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) : R :=
  (List.finRange (n - chosen.length)).foldl
    (fun acc i => acc * coeff[(⟨i.val, by
      have hi : i.val < n - chosen.length := i.isLt
      omega⟩ : Fin n)][pref[i]]) 1

private theorem partialColumnTupleCoeff_nil
    {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (coeff : Matrix R n m) (cols : Vector (Fin m) n) :
    partialColumnTupleCoeff coeff [] cols = columnTupleCoeff coeff cols := by
  unfold partialColumnTupleCoeff columnTupleCoeff
  apply foldl_det_product_congr
  intro i _hmem
  congr 2

private theorem partialColumnTupleCoeff_insertAt_last_fold
    {R : Type u} [Mul R] [OfNat R 1] {n m rem : Nat}
    (coeff : Matrix R n m) (c : Fin m) (pref : Vector (Fin m) rem)
    (hrem : rem < n) :
    (List.finRange (rem + 1)).foldl
        (fun acc i => acc * coeff[(⟨i.val, by
          have hi : i.val < rem + 1 := i.isLt
          omega⟩ : Fin n)][(insertAt c pref (Fin.last rem))[i]]) 1 =
      (List.finRange rem).foldl
          (fun acc i => acc * coeff[(⟨i.val, by
            have hi : i.val < rem := i.isLt
            omega⟩ : Fin n)][pref[i]]) 1 *
        coeff[(⟨rem, hrem⟩ : Fin n)][c] := by
  rw [List.finRange_succ_last]
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  congr 1
  · simp only [List.foldl_map]
    apply foldl_det_product_congr
    intro i _hmem
    change
      coeff[(⟨i.val, by
        have hi : i.val < rem := i.isLt
        omega⟩ : Fin n)][(insertAt c pref (Fin.last rem))[i.castSucc]] =
      coeff[(⟨i.val, by
        have hi : i.val < rem := i.isLt
        omega⟩ : Fin n)][pref[i]]
    exact congrArg
      (fun x : Fin m => coeff[(⟨i.val, by
        have hi : i.val < rem := i.isLt
        omega⟩ : Fin n)][x])
      (insertAt_last_get_castSucc c pref i)
  · change
      coeff[(⟨rem, hrem⟩ : Fin n)][(insertAt c pref (Fin.last rem))[Fin.last rem]] =
        coeff[(⟨rem, hrem⟩ : Fin n)][c]
    exact congrArg (fun x : Fin m => coeff[(⟨rem, hrem⟩ : Fin n)][x])
      (insertAt_get_self c pref (Fin.last rem))

private theorem partialColumnTupleCoeff_vectorLengthCast
    {R : Type u} [Mul R] [OfNat R 1] {n m k : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : k = n - chosen.length) (hkn : k ≤ n) (v : Vector (Fin m) k) :
    partialColumnTupleCoeff coeff chosen (vectorLengthCast hk v) =
    (List.finRange k).foldl
      (fun acc (i : Fin k) => acc *
        coeff[(⟨i.val, Nat.lt_of_lt_of_le i.isLt hkn⟩ : Fin n)][v[i]]) 1 := by
  subst hk
  unfold partialColumnTupleCoeff
  rcases v with ⟨xs, hx⟩
  rfl

private theorem partialColumnTupleCoeff_insertAt_last
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m)) (c : Fin m)
    (pref : Vector (Fin m) (n - (c :: chosen).length))
    (hk : (c :: chosen).length ≤ n)
    (hlen : (n - (c :: chosen).length) + 1 = n - chosen.length := by
      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
      omega) :
    partialColumnTupleCoeff coeff chosen
        (vectorLengthCast hlen
          (insertAt c pref (Fin.last (n - (c :: chosen).length)))) =
      coeff[(⟨n - chosen.length - 1, by
        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
        omega⟩ : Fin n)][c] *
        partialColumnTupleCoeff coeff (c :: chosen) pref := by
  have hcons : (c :: chosen).length = chosen.length + 1 := rfl
  have hrem_lt : n - (c :: chosen).length < n := by omega
  have hlen_le : (n - (c :: chosen).length) + 1 ≤ n := by omega
  rw [partialColumnTupleCoeff_vectorLengthCast coeff chosen hlen hlen_le
      (insertAt c pref (Fin.last (n - (c :: chosen).length)))]
  rw [partialColumnTupleCoeff_insertAt_last_fold coeff c pref hrem_lt]
  unfold partialColumnTupleCoeff
  refine Eq.trans (Lean.Grind.CommSemiring.mul_comm _ _) ?_
  congr 1

private theorem columnTupleVectors_suffix_rhs_step
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) :
    (columnTupleVectors ((n - (chosen.length + 1)) + 1) m).foldl
        (fun acc pref => acc +
          partialColumnTupleCoeff coeff chosen
            (vectorLengthCast (by omega : (n - (chosen.length + 1)) + 1 =
              n - chosen.length) pref) *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen
                  (vectorLengthCast (by omega : (n - (chosen.length + 1)) + 1 =
                    n - chosen.length) pref) (by omega))))) 0 =
      (List.finRange m).foldl
        (fun acc c => acc +
          coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
            (columnTupleVectors (n - (c :: chosen).length) m).foldl
              (fun acc pref => acc +
                partialColumnTupleCoeff coeff (c :: chosen) pref *
                  det (columnTupleMatrix source
                    (columnTupleVectorFn
                      (assembleColumnsSuffix (c :: chosen) pref (by
                        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                        omega))))) 0) 0 := by
  have hlen :
      n - chosen.length = (n - (chosen.length + 1)) + 1 := by
    omega
  change
    (((columnTupleVectors (n - (chosen.length + 1)) m).flatMap fun pref =>
        (List.finRange m).map fun c =>
          insertAt c pref (Fin.last (n - (chosen.length + 1)))).foldl
        (fun acc pref => acc +
          partialColumnTupleCoeff coeff chosen (vectorLengthCast hlen.symm pref) *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen (vectorLengthCast hlen.symm pref) (by omega))))) 0) =
      (List.finRange m).foldl
        (fun acc c => acc +
          coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
            (columnTupleVectors (n - (c :: chosen).length) m).foldl
              (fun acc pref => acc +
                partialColumnTupleCoeff coeff (c :: chosen) pref *
                  det (columnTupleMatrix source
                    (columnTupleVectorFn
                      (assembleColumnsSuffix (c :: chosen) pref (by
                        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                        omega))))) 0) 0
  rw [foldl_det_sum_flatMap]
  simp only [List.foldl_map]
  rw [foldl_det_sum_nested_zero]
  rw [foldl_det_sum_swap]
  apply foldl_det_sum_congr
  intro c _hc
  have hfactor :
      (columnTupleVectors (n - (chosen.length + 1)) m).foldl
          (fun acc pref => acc +
            coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
              (partialColumnTupleCoeff coeff (c :: chosen) pref *
                det (columnTupleMatrix source
                  (columnTupleVectorFn
                    (assembleColumnsSuffix (c :: chosen) pref (by
                      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                      omega)))))) 0 =
        coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
          (columnTupleVectors (n - (chosen.length + 1)) m).foldl
            (fun acc pref => acc +
              partialColumnTupleCoeff coeff (c :: chosen) pref *
                det (columnTupleMatrix source
                  (columnTupleVectorFn
                    (assembleColumnsSuffix (c :: chosen) pref (by
                      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                      omega))))) 0 := by
    exact foldl_det_sum_mul_left_zero
      (columnTupleVectors (n - (chosen.length + 1)) m)
      (coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c])
      (fun pref =>
        partialColumnTupleCoeff coeff (c :: chosen) pref *
          det (columnTupleMatrix source
            (columnTupleVectorFn
              (assembleColumnsSuffix (c :: chosen) pref (by
                have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                omega)))))
  change
    (columnTupleVectors (n - (chosen.length + 1)) m).foldl
        (fun acc' x => acc' +
          partialColumnTupleCoeff coeff chosen
              (vectorLengthCast hlen.symm (insertAt c x (Fin.last (n - (chosen.length + 1))))) *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen
                  (vectorLengthCast hlen.symm (insertAt c x (Fin.last (n - (chosen.length + 1)))))
                  (by omega))))) 0 =
      coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
        (columnTupleVectors (n - (chosen.length + 1)) m).foldl
          (fun acc pref => acc +
            partialColumnTupleCoeff coeff (c :: chosen) pref *
              det (columnTupleMatrix source
                (columnTupleVectorFn
                  (assembleColumnsSuffix (c :: chosen) pref (by
                    have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                    omega))))) 0
  rw [← hfactor]
  apply foldl_det_sum_congr
  intro pref _hpref
  have hcast :
      (n - (chosen.length + 1)) + 1 = n - chosen.length := by
    omega
  have hkcons : (c :: chosen).length ≤ n := by
    have hcons : (c :: chosen).length = chosen.length + 1 := rfl
    omega
  have hcoeff :
      partialColumnTupleCoeff coeff chosen
          (vectorLengthCast hcast
            (insertAt c pref (Fin.last (n - (chosen.length + 1))))) =
        coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
          partialColumnTupleCoeff coeff (c :: chosen) pref := by
    simpa only [List.length_cons] using
      (partialColumnTupleCoeff_insertAt_last coeff chosen c pref hkcons hcast)
  have hdet :
      det (columnTupleMatrix source
          (columnTupleVectorFn
            (assembleColumnsSuffix chosen
              (vectorLengthCast hcast
                (insertAt c pref (Fin.last (n - (chosen.length + 1)))))
              (by omega)))) =
        det (columnTupleMatrix source
          (columnTupleVectorFn (assembleColumnsSuffix (c :: chosen) pref hkcons))) := by
    simpa only [List.length_cons] using
      (det_columnTupleMatrix_assembleColumnsSuffix_insertAt_last
        source chosen c pref hkcons hcast)
  rw [hcoeff, hdet]
  grind

private theorem columnTupleVectors_suffix_rhs_step_natural
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) :
    (columnTupleVectors (n - chosen.length) m).foldl
        (fun acc pref => acc +
          partialColumnTupleCoeff coeff chosen pref *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen pref (by omega))))) 0 =
      (List.finRange m).foldl
        (fun acc c => acc +
          coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
            (columnTupleVectors (n - (c :: chosen).length) m).foldl
              (fun acc pref => acc +
                partialColumnTupleCoeff coeff (c :: chosen) pref *
                  det (columnTupleMatrix source
                    (columnTupleVectorFn
                      (assembleColumnsSuffix (c :: chosen) pref (by
                        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                        omega))))) 0) 0 := by
  rw [columnTupleVectors_foldl_vectorLengthCast
    (by omega : (n - (chosen.length + 1)) + 1 = n - chosen.length)]
  exact columnTupleVectors_suffix_rhs_step source coeff chosen hk

private theorem assembleColumnsSuffix_full
    {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length))
    (hk : chosen.length ≤ n) (hfull : chosen.length = n) :
    assembleColumnsSuffix chosen pref hk =
      Vector.ofFn (fun j : Fin n => chosen[j.val]'(by omega)) := by
  apply Vector.ext
  intro i hi
  change (assembleColumnsSuffix chosen pref hk)[(⟨i, hi⟩ : Fin n)] =
    (Vector.ofFn (fun j : Fin n => chosen[j.val]'(by omega)))[(⟨i, hi⟩ : Fin n)]
  simpa [hfull] using
    (assembleColumnsSuffix_right chosen pref hk (⟨i, by omega⟩ : Fin chosen.length))

private theorem partialColumnTupleCoeff_full
    {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length))
    (hfull : chosen.length = n) :
    partialColumnTupleCoeff coeff chosen pref = 1 := by
  subst n
  unfold partialColumnTupleCoeff
  have hlist : List.finRange (chosen.length - chosen.length) = [] := by simp
  rw [hlist]
  rfl

private theorem det_columnSumMatrixWithSuffix_eq_sum
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length ≤ n) :
    det (columnSumMatrixWithSuffix source coeff chosen) =
      (columnTupleVectors (n - chosen.length) m).foldl
        (fun acc pref => acc +
          partialColumnTupleCoeff coeff chosen pref *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen pref hk)))) 0 := by
  by_cases hfull : chosen.length = n
  ·
      have hfull : chosen.length = n := by omega
      subst n
      rw [columnSumMatrixWithSuffix_eq source coeff chosen hfull]
      let hcast : 0 = chosen.length - chosen.length := by omega
      rw [columnTupleVectors_foldl_vectorLengthCast hcast]
      simp only [columnTupleVectors, List.foldl_cons, List.foldl_nil]
      rw [partialColumnTupleCoeff_full coeff chosen (vectorLengthCast hcast emptyVec) hfull]
      have hdet :
          det (columnTupleMatrix source (fun j : Fin chosen.length => chosen[j.val]'(by omega))) =
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen (vectorLengthCast hcast emptyVec) hk))) := by
        apply congrArg det
        apply congrArg (columnTupleMatrix source)
        funext j
        simp [columnTupleVectorFn]
        rw [assembleColumnsSuffix_full chosen (vectorLengthCast hcast emptyVec) hk hfull]
        simp
      rw [hdet]
      grind
  ·
      have hklt : chosen.length < n := by omega
      rw [det_columnSumMatrixWithSuffix_expand source coeff chosen hklt]
      rw [columnTupleVectors_suffix_rhs_step_natural source coeff chosen hklt]
      apply foldl_det_sum_congr
      intro c _hc
      congr 2
      have hkcons : (c :: chosen).length ≤ n := by
        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
        omega
      exact det_columnSumMatrixWithSuffix_eq_sum source coeff (c :: chosen) hkcons
termination_by n - chosen.length
decreasing_by
  simp_wf
  omega

/-- Expand the determinant of a matrix whose columns are linear combinations
of source columns as a finite sum over all ordered column tuples. This is the
Mathlib-free multilinearity form behind Cauchy-Binet. -/
theorem det_columnSumMatrix_eq_sum_columnTuples
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) :
    det (columnSumMatrix source coeff) =
      (columnTupleVectors n m).foldl
        (fun acc cols => acc +
          columnTupleCoeff coeff cols *
            det (columnTupleMatrix source (columnTupleVectorFn cols))) 0 := by
  rw [← columnSumMatrixWithSuffix_nil source coeff]
  rw [det_columnSumMatrixWithSuffix_eq_sum source coeff [] (by simp)]
  apply foldl_det_sum_congr
  intro cols _hcols
  have hcoeff : partialColumnTupleCoeff coeff [] cols = columnTupleCoeff coeff cols :=
    partialColumnTupleCoeff_nil coeff cols
  have hdet :
      det (columnTupleMatrix source (columnTupleVectorFn (assembleColumnsSuffix [] cols (by simp)))) =
        det (columnTupleMatrix source (columnTupleVectorFn cols)) := by
    apply congrArg det
    apply Vector.ext
    intro i hi
    change (columnTupleMatrix source (columnTupleVectorFn (assembleColumnsSuffix [] cols (by simp))))[
        (⟨i, hi⟩ : Fin n)] =
      (columnTupleMatrix source (columnTupleVectorFn cols))[(⟨i, hi⟩ : Fin n)]
    apply Vector.ext
    intro j hj
    simp [columnTupleMatrix, columnTupleVectorFn, ofFn]
    change source[(⟨i, hi⟩ : Fin n)][
        (assembleColumnsSuffix [] cols (by simp))[(⟨j, hj⟩ : Fin n)]] =
      source[(⟨i, hi⟩ : Fin n)][cols[(⟨j, hj⟩ : Fin n)]]
    exact congrArg (fun x : Fin m => source[(⟨i, hi⟩ : Fin n)][x])
      (assembleColumnsSuffix_left ([] : List (Fin m)) cols (by simp) (⟨j, by simp [hj]⟩))
  rw [hcoeff, hdet]

/-- The determinant of a row Gram matrix expands as the ordered-column tuple
sum induced by the generic column-sum determinant expansion. -/
theorem det_gramMatrix_eq_sum_columnTuples
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat} (A : Matrix R n m) :
    det (gramMatrix A) =
      (columnTupleVectors n m).foldl
        (fun acc cols => acc +
          columnTupleCoeff A cols *
            det (columnTupleMatrix A (columnTupleVectorFn cols))) 0 := by
  have hgram : gramMatrix A = columnSumMatrix A A := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro c hc
    change (gramMatrix A)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix A A)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
    rw [columnSumMatrix_entry]
    simp [gramMatrix, ofFn, row, Hex.Vector.dotProduct]
    apply foldl_det_sum_congr
    intro k _hk
    exact Lean.Grind.CommSemiring.mul_comm A[(⟨r, hr⟩ : Fin n)][k] A[(⟨c, hc⟩ : Fin n)][k]
  rw [hgram]
  exact det_columnSumMatrix_eq_sum_columnTuples A A


end Matrix
end Hex
