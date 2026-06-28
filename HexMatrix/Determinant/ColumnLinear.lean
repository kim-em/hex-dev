/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Determinant.Permutation
import all HexMatrix.Determinant.Permutation

public section

/-!
Determinant column linearity for `hex-matrix`.

This module proves that `det` is multilinear in a single replaced column.
Working from the per-permutation product `detProduct` and signed term
`detTerm`, it establishes the additive `det_setCol_add`, the scalar
`det_setCol_smul`, and the finite-list/`Fin m` aggregated forms
`det_setCol_sum_list` and `det_setCol_sum_finRange`. It also collects the
duplicate-column/row vanishing lemmas (`det_eq_zero_of_col_eq`,
`det_eq_zero_of_row_eq`) and `det_setCol_add_otherCols` (column operations
preserve the determinant), plus the `columnSumMatrix` builder and the Fubini
sum-swap `foldl_det_sum_swap` used by the Cauchy-Binet expansion.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- The per-permutation product `detProduct` is additive in the replaced
column: splitting that column's entries as `v + w` splits the product as a sum. -/
private theorem detProduct_setCol_add {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct (setCol M dst (fun r => v r + w r)) perm =
      detProduct (setCol M dst v) perm +
        detProduct (setCol M dst w) perm := by
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
        (fun acc i => acc * (setCol M dst (fun r => v r + w r))[i][perm[i]]) 1 =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            (setCol M dst v)[x][perm[x]] + (setCol M dst w)[x][perm[x]]
          else
            (setCol M dst v)[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        rw [setCol_getElem, setCol_getElem, setCol_getElem]
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
            (setCol M dst v)[x][perm[x]] + (1 : R) * (setCol M dst w)[x][perm[x]]
          else
            (setCol M dst v)[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        by_cases hxp : x = pivot
        · rw [if_pos hxp]
          grind
        · simp [hxp]
    _ =
      (List.finRange n).foldl
          (fun acc x => acc * (setCol M dst v)[x][perm[x]]) 1 +
        (1 : R) * (List.finRange n).foldl
          (fun acc x => acc * (setCol M dst w)[x][perm[x]]) 1 := by
        exact
          foldl_det_product_single_add (R := R) (β := Fin n)
            (List.finRange n) pivot (1 : R)
            (fun x => (setCol M dst v)[x][perm[x]])
            (fun x => (setCol M dst w)[x][perm[x]])
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
              change (setCol M dst w)[x][perm[x]] =
                (setCol M dst v)[x][perm[x]]
              rw [setCol_getElem, setCol_getElem]
              change (if perm[x] = dst then w x else M[x][perm[x]]) =
                (if perm[x] = dst then v x else M[x][perm[x]])
              rw [if_neg hperm_ne, if_neg hperm_ne])
    _ =
      (List.finRange n).foldl
          (fun acc x => acc * (setCol M dst v)[x][perm[x]]) 1 +
        (List.finRange n).foldl
          (fun acc x => acc * (setCol M dst w)[x][perm[x]]) 1 := by
        grind

/-- The per-permutation product `detProduct` is homogeneous in the replaced
column: scaling that column's entries by `c` scales the product by `c`. -/
private theorem detProduct_setCol_smul {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct (setCol M dst (fun r => c * v r)) perm =
      c * detProduct (setCol M dst v) perm := by
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
        (fun acc i => acc * (setCol M dst (fun r => c * v r))[i][perm[i]]) 1 =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            c * (setCol M dst v)[x][perm[x]]
          else
            (setCol M dst v)[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        rw [setCol_getElem, setCol_getElem]
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
          (fun acc x => acc * (setCol M dst v)[x][perm[x]]) 1 := by
        exact
          foldl_det_product_single_scale (R := R) (β := Fin n)
            (List.finRange n) pivot c
            (fun x => (setCol M dst v)[x][perm[x]])
            1 (List.mem_finRange pivot) (List.nodup_finRange n)

/-- The signed Leibniz term `detTerm` is additive in the replaced column:
splitting that column's entries as `v + w` splits the term as a sum. -/
private theorem detTerm_setCol_add {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (setCol M dst (fun r => v r + w r)) perm =
      detTerm (setCol M dst v) perm + detTerm (setCol M dst w) perm := by
  unfold detTerm
  rw [detProduct_setCol_add M dst v w perm hnodup]
  grind

/-- The signed Leibniz term `detTerm` is homogeneous in the replaced column:
scaling that column's entries by `c` scales the term by `c`. -/
private theorem detTerm_setCol_smul {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (setCol M dst (fun r => c * v r)) perm =
      c * detTerm (setCol M dst v) perm := by
  unfold detTerm
  rw [detProduct_setCol_smul M dst c v perm hnodup]
  grind

/-- Determinant linearity in one replaced column, additive form. -/
theorem det_setCol_add {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R) :
    det (setCol M dst (fun r => v r + w r)) =
      det (setCol M dst v) + det (setCol M dst w) := by
  simp [det]
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (setCol M dst (fun r => v r + w r)) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm =>
          acc + (detTerm (setCol M dst v) perm +
            detTerm (setCol M dst w) perm)) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        exact detTerm_setCol_add M dst v w perm (permutationVectors_nodup hmem)
    _ =
      (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (setCol M dst v) perm) 0 +
        (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (setCol M dst w) perm) 0 := by
        exact foldl_det_sum_add_zero
          (permutationVectors n)
          (detTerm (setCol M dst v))
          (detTerm (setCol M dst w))

/-- Determinant linearity in one replaced column, scalar form. -/
theorem det_setCol_smul {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R) :
    det (setCol M dst (fun r => c * v r)) =
      c * det (setCol M dst v) := by
  simp [det]
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (setCol M dst (fun r => c * v r)) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + c * detTerm (setCol M dst v) perm) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        exact detTerm_setCol_smul M dst c v perm (permutationVectors_nodup hmem)
    _ =
      c * (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (setCol M dst v) perm) 0 := by
        exact foldl_det_sum_mul_left_zero
          (permutationVectors n) c (detTerm (setCol M dst v))

/-- The assembled determinant `det` vanishes when the replaced column is zero. -/
private theorem det_setCol_zero {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) :
    det (setCol M dst (fun _ => (0 : R))) = 0 := by
  have h := det_setCol_smul M dst (0 : R) (fun _ => (1 : R))
  have hcol : (fun r : Fin n => (0 : R) * (1 : R)) = fun _ => (0 : R) := by
    funext r
    grind
  rw [hcol] at h
  grind

/-- Determinant linearity in one replaced column, finite-list form. -/
theorem det_setCol_sum_list {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) {β : Type v} (xs : List β)
    (coeff : β → R) (source : β → Fin n → R) :
    det (setCol M dst
        (fun r => xs.foldl (fun acc x => acc + coeff x * source x r) 0)) =
      xs.foldl
        (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 := by
  induction xs with
  | nil =>
      exact det_setCol_zero M dst
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
        det (setCol M dst
            (fun r => xs.foldl (fun acc x => acc + coeff x * source x r)
              (0 + coeff x * source x r))) =
          det (setCol M dst (fun r => coeff x * source x r + tail r)) := by
            rw [hcol]
        _ =
          det (setCol M dst (fun r => coeff x * source x r)) +
            det (setCol M dst tail) := by
            exact det_setCol_add M dst (fun r => coeff x * source x r) tail
        _ =
          coeff x * det (setCol M dst (source x)) +
            xs.foldl (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 := by
            rw [det_setCol_smul]
            simp [tail]
            rw [ih]
        _ =
          xs.foldl (fun acc x => acc + coeff x * det (setCol M dst (source x)))
            (0 + coeff x * det (setCol M dst (source x))) := by
            have hstart :=
              (foldl_det_sum_start (R := R) xs
                (fun x => coeff x * det (setCol M dst (source x)))
                (0 + coeff x * det (setCol M dst (source x)))).symm
            calc
              coeff x * det (setCol M dst (source x)) +
                  xs.foldl
                    (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 =
                (0 + coeff x * det (setCol M dst (source x))) +
                  xs.foldl
                    (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 := by
                  grind
              _ =
                xs.foldl
                  (fun acc x => acc + coeff x * det (setCol M dst (source x)))
                  (0 + coeff x * det (setCol M dst (source x))) := hstart

/-- Determinant linearity in one replaced column, indexed by `Fin m`. -/
theorem det_setCol_sum_finRange {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (M : Matrix R n n) (dst : Fin n) (coeff : Fin m → R)
    (source : Fin m → Fin n → R) :
    det (setCol M dst
        (fun r => (List.finRange m).foldl
          (fun acc x => acc + coeff x * source x r) 0)) =
      (List.finRange m).foldl
        (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 :=
  det_setCol_sum_list M dst (List.finRange m) coeff source

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

private theorem setCol_columnSumMatrix_self
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (dst : Fin n) :
    setCol (columnSumMatrix source coeff) dst
        (fun r => (List.finRange m).foldl
          (fun acc k => acc + coeff[dst][k] * source[r][k]) 0) =
      columnSumMatrix source coeff := by
  ext r hr c hc
  change
    (setCol (columnSumMatrix source coeff) dst
        (fun r => (List.finRange m).foldl
          (fun acc k => acc + coeff[dst][k] * source[r][k]) 0))[
          (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix source coeff)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [setCol_getElem]
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
            det (setCol (columnSumMatrix source coeff) dst (fun r => source[r][k]))) 0 := by
  have hsum :=
    det_setCol_sum_list
    (columnSumMatrix source coeff) dst (List.finRange m)
    (fun k => coeff[dst][k]) (fun k r => source[r][k])
  have hself := setCol_columnSumMatrix_self source coeff dst
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
    ext r hr c hc
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
theorem det_setCol_existing_col_eq_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst src : Fin n) (hsrcdst : src ≠ dst) :
    det (setCol M dst (fun r => M[r][src])) = 0 := by
  apply det_eq_zero_of_col_eq (setCol M dst (fun r => M[r][src])) src dst hsrcdst
  intro r
  rw [setCol_getElem, setCol_getElem]
  rw [if_neg hsrcdst, if_pos rfl]

/-- Adding a finite linear combination of other columns of `M` to column `dst`
preserves the determinant. The sources are given as a list and each source is
required to differ from `dst`. -/
theorem det_setCol_add_otherCols {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (sources : List (Fin n)) (coeff : Fin n → R)
    (hsrc : ∀ s ∈ sources, s ≠ dst) :
    det (setCol M dst
        (fun r => M[r][dst] +
          sources.foldl (fun acc s => acc + coeff s * M[r][s]) 0)) = det M := by
  rw [det_setCol_add M dst (fun r => M[r][dst])
    (fun r => sources.foldl (fun acc s => acc + coeff s * M[r][s]) 0)]
  rw [setCol_self M dst]
  have hcomb : det (setCol M dst
        (fun r => sources.foldl (fun acc s => acc + coeff s * M[r][s]) 0)) = 0 := by
    rw [det_setCol_sum_list M dst sources coeff (fun s r => M[r][s])]
    -- Show each summand is zero; we use the fact that the foldl over sources
    -- yields zero because each replaced det is zero.
    have hzero_each : ∀ s ∈ sources, coeff s * det (setCol M dst (fun r => M[r][s])) = 0 := by
      intro s hs
      have hne : s ≠ dst := hsrc s hs
      rw [det_setCol_existing_col_eq_zero M dst s hne]
      grind
    -- Foldl of a sum that is always zero adds nothing.
    have hfoldl : sources.foldl
        (fun acc s => acc + coeff s * det (setCol M dst (fun r => M[r][s]))) 0 = 0 := by
      clear hzero_each
      induction sources with
      | nil => rfl
      | cons s ss ih =>
          simp only [List.foldl_cons]
          have hs : coeff s * det (setCol M dst (fun r => M[r][s])) = 0 := by
            have hne : s ≠ dst := hsrc s (by simp)
            rw [det_setCol_existing_col_eq_zero M dst s hne]
            grind
          rw [hs]
          have hsrc' : ∀ s' ∈ ss, s' ≠ dst := fun s' hs' => hsrc s' (by simp [hs'])
          have hzero_acc : (0 : R) + 0 = 0 := by grind
          rw [hzero_acc]
          exact ih hsrc'
    exact hfoldl
  rw [hcomb]
  grind

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


end Matrix
end Hex
