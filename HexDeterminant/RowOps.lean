/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminant.Permutation
import all HexDeterminant.Permutation

public section

/-!
Determinant of elementary row and column operations.

Building on the permutation-vector structure in `HexDeterminant.Permutation`,
this module reindexes the Leibniz sum to read off the determinant's reaction to
the elementary operations: `det_identity`, `det_rowSwap`, `det_rowScale`,
`det_rowAdd`, `det_transpose`, `cofactor_transpose`, and the column analogues
`det_colPermute_vector`, `det_colSwap`, `det_colAdd`.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

private theorem detTerm_identity_insertAt_last {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) :
    detTerm (Matrix.identity (R := R) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detTerm (Matrix.identity (R := R) n) v := by
  unfold detTerm
  rw [detSign_insertAt_last, detProduct_identity_insertAt_last]

private theorem foldl_detTerm_identity_insertions {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) (z : R) :
    (List.finRange (n + 1)).foldl
        (fun acc i =>
          acc + detTerm (Matrix.identity (R := R) (n + 1))
            (insertAt (Fin.last n) (v.map Fin.castSucc) i)) z =
      z + detTerm (Matrix.identity (R := R) n) v := by
  rw [← Fin.foldl_eq_finRange_foldl, Fin.foldl_succ_last]
  have hprefix :
      Fin.foldl n
          (fun acc i =>
            acc + detTerm (Matrix.identity (R := R) (n + 1))
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z = z := by
    rw [Fin.foldl_eq_finRange_foldl]
    calc
      (List.finRange n).foldl
          (fun acc i =>
            acc + detTerm (Matrix.identity (R := R) (n + 1))
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z =
        (List.finRange n).foldl (fun acc (_i : Fin n) => acc + (0 : R)) z := by
          apply List.foldl_add_congr
          intro i _hmem
          unfold detTerm
          rw [detProduct_identity_insertAt_not_last_zero (R := R) v i.castSucc (by
            intro hlast
            have hval := congrArg Fin.val hlast
            simp at hval
            exact (Nat.ne_of_lt i.isLt) hval)]
          grind
      _ = z := by
          exact List.foldl_add_zero (List.finRange n) z
  rw [hprefix, detTerm_identity_insertAt_last]

private theorem rowScale_get {R : Type u} [Mul R] {n m : Nat}
    (M : Matrix R n m) (i r : Fin n) (c : R) (k : Fin m) :
    (rowScale M i c)[r][k] = if r = i then c * M[i][k] else M[r][k] :=
  getElem_rowScale M i r c k

private theorem detProduct_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detProduct (rowScale M i c) perm = c * detProduct M perm := by
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc r => acc * (rowScale M i c)[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r => acc * if r = i then c * M[r][perm[r]] else M[r][perm[r]]) 1 := by
        apply List.foldl_mul_congr
        intro r _hmem
        by_cases h : r = i
        · subst r
          simpa using (rowScale_get M i i c perm[i])
        · simpa [h] using (rowScale_get M i r c perm[r])
    _ = c * (List.finRange n).foldl (fun acc r => acc * M[r][perm[r]]) 1 := by
        exact foldl_det_product_single_scale
          (List.finRange n) i c (fun r => M[r][perm[r]]) 1
          (List.mem_finRange i) (List.nodup_finRange n)


private theorem swapPermutationValues_idxOf_left {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    (swapPermutationValues perm i j).toList.idxOf i = perm.toList.idxOf j := by
  let pi : Fin n := ⟨perm.toList.idxOf i,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt i (by simp [Vector.length_toList]) hnodup⟩
  let pj : Fin n := ⟨perm.toList.idxOf j,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt j (by simp [Vector.length_toList]) hnodup⟩
  have hpi_get : perm[pi] = i := by
    have hlt : perm.toList.idxOf i < perm.toList.length := by
      simpa [pi, Vector.length_toList] using pi.isLt
    exact List.getElem_idxOf (x := i) (xs := perm.toList) hlt
  have hswap :
      swapPermutationValues perm i j = transposePermutationValues perm pi pj := by
    simpa [pi, pj] using swapPermutationValues_eq perm i j hnodup
  have hpj_swap : (swapPermutationValues perm i j)[pj] = i := by
    rw [hswap, transposePermutationValues_get]
    calc
      perm[finTranspose pi pj pj] = perm[pi] := by
        exact congrArg (fun x => perm[x]) (finTranspose_right pi pj)
      _ = i := hpi_get
  have hnodupSwap := swapPermutationValues_toList_nodup perm i j hnodup
  have hpjLen : pj.val < (swapPermutationValues perm i j).toList.length := by
    simp [Vector.length_toList]
  have hidx :
      (swapPermutationValues perm i j).toList.idxOf
          ((swapPermutationValues perm i j).toList[pj.val]'hpjLen) = pj.val := by
    exact hnodupSwap.idxOf_getElem pj.val hpjLen
  have hget :
      (swapPermutationValues perm i j).toList[pj.val]'hpjLen = i := by
    exact hpj_swap
  rw [hget] at hidx
  exact hidx

private theorem swapPermutationValues_idxOf_right {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    (swapPermutationValues perm i j).toList.idxOf j = perm.toList.idxOf i := by
  have hcomm : swapPermutationValues perm i j = swapPermutationValues perm j i := by
    ext r hr
    apply Fin.val_eq_of_eq
    change (swapPermutationValues perm i j)[(⟨r, hr⟩ : Fin n)] =
      (swapPermutationValues perm j i)[(⟨r, hr⟩ : Fin n)]
    repeat rw [swapPermutationValues_get]
    by_cases hpi : perm[(⟨r, hr⟩ : Fin n)] = i
    · rw [hpi]
      exact (finTranspose_left i j).trans (finTranspose_right j i).symm
    · by_cases hpj : perm[(⟨r, hr⟩ : Fin n)] = j
      · rw [hpj]
        exact (finTranspose_right i j).trans (finTranspose_left j i).symm
      · exact
          (finTranspose_of_ne i j perm[(⟨r, hr⟩ : Fin n)] hpi hpj).trans
            (finTranspose_of_ne j i perm[(⟨r, hr⟩ : Fin n)] hpj hpi).symm
  rw [hcomm]
  exact swapPermutationValues_idxOf_left perm j i hnodup

private theorem permutation_idxOf_ne {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    perm.toList.idxOf i ≠ perm.toList.idxOf j := by
  intro hidx
  have hiLt : perm.toList.idxOf i < perm.toList.length :=
    fin_idxOf_lt i (by simp [Vector.length_toList]) hnodup
  have hjLt : perm.toList.idxOf j < perm.toList.length :=
    fin_idxOf_lt j (by simp [Vector.length_toList]) hnodup
  have hiGet : perm.toList[perm.toList.idxOf i]'hiLt = i :=
    List.getElem_idxOf (x := i) (xs := perm.toList) hiLt
  have hjGet : perm.toList[perm.toList.idxOf j]'hjLt = j :=
    List.getElem_idxOf (x := j) (xs := perm.toList) hjLt
  apply h
  have hfin :
      (⟨perm.toList.idxOf i, hiLt⟩ : Fin perm.toList.length) =
        ⟨perm.toList.idxOf j, hjLt⟩ := Fin.ext hidx
  have hgeteq := congrArg (fun k : Fin perm.toList.length => perm.toList[k]) hfin
  exact hiGet.symm.trans (hgeteq.trans hjGet)

/-- When columns `src` and `dst` of `M` are equal, swapping those two values
in a permutation leaves the product term `detProduct M perm` unchanged. -/
private theorem detProduct_colDuplicate_swapValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst])
    (perm : Vector (Fin n) n) :
    detProduct M perm = detProduct M (swapPermutationValues perm src dst) := by
  unfold detProduct
  apply List.foldl_mul_congr
  intro r _hmem
  by_cases hsrc : perm[r] = src
  · have hswap : (swapPermutationValues perm src dst)[r] = dst := by
      rw [swapPermutationValues_get]
      exact hsrc ▸ finTranspose_left src dst
    calc
      M[r][perm[r]] = M[r][src] := congrArg (fun c => M[r][c]) hsrc
      _ = M[r][dst] := hcol r
      _ = M[r][(swapPermutationValues perm src dst)[r]] :=
          (congrArg (fun c => M[r][c]) hswap).symm
  · by_cases hdst : perm[r] = dst
    · have hswap : (swapPermutationValues perm src dst)[r] = src := by
        rw [swapPermutationValues_get]
        exact hdst ▸ finTranspose_right src dst
      calc
        M[r][perm[r]] = M[r][dst] := congrArg (fun c => M[r][c]) hdst
        _ = M[r][src] := (hcol r).symm
        _ = M[r][(swapPermutationValues perm src dst)[r]] :=
            (congrArg (fun c => M[r][c]) hswap).symm
    · have hswap : (swapPermutationValues perm src dst)[r] = perm[r] := by
        rw [swapPermutationValues_get]
        exact finTranspose_of_ne src dst perm[r] hsrc hdst
      exact (congrArg (fun c => M[r][c]) hswap).symm

/-- For a nodup permutation with `src ≠ dst` and equal columns `src`, `dst`,
swapping those two values negates the signed determinant term `detTerm M perm`. -/
private theorem detTerm_colDuplicate_swapValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst])
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm M perm = -detTerm M (swapPermutationValues perm src dst) := by
  unfold detTerm
  rw [detProduct_colDuplicate_swapValues M src dst hcol perm,
    detSign_swapPermutationValues (R := R) perm src dst hnodup h]
  grind

/-- `M` with column `dst` overwritten by a copy of column `src`. -/
private def colAddDuplicate {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) : Matrix R n n :=
  Matrix.ofFn fun r c => if c = dst then M[r][src] else M[r][c]

/-- Entrywise value of `colAddDuplicate M src dst`: column `dst` reads from
column `src`, every other column is left unchanged. -/
private theorem colAddDuplicate_get {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst r c : Fin n) :
    (colAddDuplicate M src dst)[r][c] = if c = dst then M[r][src] else M[r][c] := by
  simp [colAddDuplicate, Matrix.ofFn]

/-- Entrywise value of `colAdd M src dst c`: column `dst` becomes
`M[r][dst] + c · M[r][src]`, every other column is left unchanged. -/
private theorem colAdd_get {R : Type u} [Mul R] [Add R] {n : Nat}
    (M : Matrix R n n) (src dst r cidx : Fin n) (c : R) :
    (colAdd M src dst c)[r][cidx] =
      if cidx = dst then M[r][cidx] + c * M[r][src] else M[r][cidx] := by
  exact getElem_colAdd M src dst c r cidx

/-- For a nodup permutation, the product term of `colAdd M src dst c` splits as
`detProduct M perm + c · detProduct (colAddDuplicate M src dst) perm`. -/
private theorem detProduct_colAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct (colAdd M src dst c) perm =
      detProduct M perm + c * detProduct (colAddDuplicate M src dst) perm := by
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
        (fun acc i => acc * (colAdd M src dst c)[i][perm[i]]) 1 =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            M[x][perm[x]] + c * (colAddDuplicate M src dst)[x][perm[x]]
          else
            M[x][perm[x]]) 1 := by
        apply List.foldl_mul_congr
        intro x _hx
        rw [colAdd_get]
        by_cases hxp : x = pivot
        · subst x
          rw [if_pos hpivot, if_pos rfl, colAddDuplicate_get, if_pos hpivot]
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
          rw [if_neg hperm_ne]
    _ =
      (List.finRange n).foldl (fun acc x => acc * M[x][perm[x]]) 1 +
        c * (List.finRange n).foldl
          (fun acc x => acc * (colAddDuplicate M src dst)[x][perm[x]]) 1 := by
      exact
        foldl_det_product_single_add (R := R) (β := Fin n)
          (List.finRange n) pivot c
          (fun x => M[x][perm[x]])
          (fun x => (colAddDuplicate M src dst)[x][perm[x]])
          1 (List.mem_finRange pivot) (List.nodup_finRange n)
          (by
            intro x _hx hxp
            change (colAddDuplicate M src dst)[x][perm[x]] = M[x][perm[x]]
            rw [colAddDuplicate_get]
            have hperm_ne : perm[x] ≠ dst := by
              intro hperm
              have hxidx : perm.toList.idxOf perm[x] = x.val := by
                simpa [Vector.getElem_toList, Vector.length_toList] using
                  hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
              have hpidx : perm.toList.idxOf dst = pivot.val := rfl
              have hval : x.val = pivot.val := by
                rw [← hxidx, hperm, hpidx]
              exact hxp (Fin.ext hval)
            rw [if_neg hperm_ne])

/-- For a nodup permutation, the signed term of `colAdd M src dst c` splits as
`detTerm M perm + c · detTerm (colAddDuplicate M src dst) perm`. -/
private theorem detTerm_colAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (colAdd M src dst c) perm =
      detTerm M perm + c * detTerm (colAddDuplicate M src dst) perm := by
  unfold detTerm
  rw [detProduct_colAdd M src dst c perm hnodup]
  grind

private theorem detTerm_rowSwap_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (rowSwap M i j) perm =
      -detTerm M (transposePermutationValues perm i j) := by
  unfold detTerm
  rw [detProduct_rowSwap_transposeValues M i j h perm,
    detSign_transposeValues (R := R) perm i j hnodup h]
  grind

private theorem permutationVectors_transposeValues_neg_sum {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (_h : i ≠ j) :
    (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M (transposePermutationValues perm i j)) 0 =
      -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M (transposePermutationValues perm i j)) 0 =
      ((permutationVectors n).map fun perm => transposePermutationValues perm i j).foldl
        (fun acc perm => acc + -detTerm M perm) 0 := by
        simp [List.foldl_map]
    _ =
      (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M perm) 0 := by
        exact List.foldl_add_perm
          (fun perm => -detTerm M perm)
          (transposePermutationValues_map_permutationVectors_perm i j) 0
    _ =
      (permutationVectors n).foldl
        (fun acc perm => acc + (-1 : R) * detTerm M perm) 0 := by
        apply List.foldl_add_congr
        intro perm _hmem
        grind
    _ =
      (-1 : R) *
        ((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        exact List.foldl_add_mul_left_zero (permutationVectors n) (-1 : R) (detTerm M)
    _ = -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        grind

/-- The permutation-vector enumeration contributes `1` on the identity
matrix: all non-identity terms vanish and the identity vector appears once. -/
private theorem permutationVectors_identity_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (Matrix.identity (R := R) n) perm) 0 = 1 := by
  induction n with
  | zero =>
      simp [permutationVectors, detTerm, detSign, detProduct, inversionCount]
      grind
  | succ n ih =>
      simp only [permutationVectors]
      rw [List.foldl_add_flatMap]
      simp only [List.foldl_map, foldl_detTerm_identity_insertions]
      exact ih

/-- Row swapping pairs the permutation-vector Leibniz terms with opposite sign. -/
private theorem permutationVectors_rowSwap_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowSwap M i j) perm) 0 =
      -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowSwap M i j) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M (transposePermutationValues perm i j)) 0 := by
        apply List.foldl_add_congr
        intro perm hmem
        exact detTerm_rowSwap_transposeValues M i j h perm (permutationVectors_nodup hmem)
    _ = -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        exact permutationVectors_transposeValues_neg_sum M i j h

/-- Scaling one matrix row scales each Leibniz term by the same scalar. -/
private theorem detTerm_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detTerm (rowScale M i c) perm = c * detTerm M perm := by
  unfold detTerm
  rw [detProduct_rowScale]
  grind

/-- `M` with row `dst` overwritten by a copy of row `src` (row analogue of
`colAddDuplicate`). -/
private def rowAddDuplicate {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) : Matrix R n n :=
  M.set dst M[src]

/-- Entrywise value of `rowAdd M src dst c`: row `dst` becomes
`M[dst][k] + c · M[src][k]`, every other row is left unchanged. -/
private theorem rowAdd_get {R : Type u} [Mul R] [Add R] {n : Nat}
    (M : Matrix R n n) (src dst r : Fin n) (c : R) (k : Fin n) :
    (rowAdd M src dst c)[r][k] =
      if r = dst then M[dst][k] + c * M[src][k] else M[r][k] :=
  getElem_rowAdd M src dst r c k

/-- Entrywise value of `rowAddDuplicate M src dst`: row `dst` reads from row
`src`, every other row is left unchanged. -/
private theorem rowAddDuplicate_get {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst r : Fin n) (k : Fin n) :
    (rowAddDuplicate M src dst)[r][k] =
      if r = dst then M[src][k] else M[r][k] := by
  by_cases h : r = dst
  · subst r
    simp [rowAddDuplicate]
  · simp [rowAddDuplicate, h]
    have hval : dst.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow : (M.set dst M[src])[r] = M[r] := by
      exact (Vector.getElem_set_ne (xs := M) (x := M[src]) dst.isLt r.isLt hval)
    simpa [rowAddDuplicate] using congrArg (fun row => row[k]) hrow

/-- The product term of `rowAdd M src dst c` splits as
`detProduct M perm + c · detProduct (rowAddDuplicate M src dst) perm`. -/
private theorem detProduct_rowAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detProduct (rowAdd M src dst c) perm =
      detProduct M perm + c * detProduct (rowAddDuplicate M src dst) perm := by
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc r => acc * (rowAdd M src dst c)[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r =>
          acc * if r = dst then
            M[r][perm[r]] + c * (rowAddDuplicate M src dst)[r][perm[r]]
          else
            M[r][perm[r]]) 1 := by
        apply List.foldl_mul_congr
        intro r _hmem
        by_cases h : r = dst
        · subst r
          rw [rowAdd_get M src dst dst c perm[dst], rowAddDuplicate_get M src dst dst perm[dst]]
          simp
        · rw [rowAdd_get, rowAddDuplicate_get]
          simp [h]
    _ =
      (List.finRange n).foldl (fun acc r => acc * M[r][perm[r]]) 1 +
        c * (List.finRange n).foldl
          (fun acc r => acc * (rowAddDuplicate M src dst)[r][perm[r]]) 1 := by
        exact foldl_det_product_single_add
          (List.finRange n) dst c
          (fun r => M[r][perm[r]])
          (fun r => (rowAddDuplicate M src dst)[r][perm[r]]) 1
          (List.mem_finRange dst) (List.nodup_finRange n)
          (fun r _hmem hne => by
            change (rowAddDuplicate M src dst)[r][perm[r]] = M[r][perm[r]]
            rw [rowAddDuplicate_get]
            simp [hne])

/-- The signed term of `rowAdd M src dst c` splits as
`detTerm M perm + c · detTerm (rowAddDuplicate M src dst) perm`. -/
private theorem detTerm_rowAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detTerm (rowAdd M src dst c) perm =
      detTerm M perm + c * detTerm (rowAddDuplicate M src dst) perm := by
  unfold detTerm
  rw [detProduct_rowAdd]
  grind

private theorem foldl_sum_filter_split_start {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (p : β → Bool) (f : β → R) :
    ∀ a b : R,
      xs.foldl (fun acc x => acc + f x) (a + b) =
        (xs.filter p).foldl (fun acc x => acc + f x) a +
          (xs.filter fun x => !p x).foldl (fun acc x => acc + f x) b := by
  induction xs with
  | nil =>
      intro a b
      rfl
  | cons x xs ih =>
      intro a b
      simp only [List.foldl_cons]
      by_cases hp : p x
      · simp [hp]
        have hstart : a + b + f x = a + f x + b := by grind
        rw [hstart]
        exact ih (a + f x) b
      · simp [hp]
        have hstart : a + b + f x = a + (b + f x) := by grind
        rw [hstart]
        exact ih a (b + f x)

private theorem foldl_sum_filter_split {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (p : β → Bool) (f : β → R) :
    xs.foldl (fun acc x => acc + f x) 0 =
      (xs.filter p).foldl (fun acc x => acc + f x) 0 +
        (xs.filter fun x => !p x).foldl (fun acc x => acc + f x) 0 := by
  calc
    xs.foldl (fun acc x => acc + f x) 0 =
      xs.foldl (fun acc x => acc + f x) ((0 : R) + 0) := by
        have hzero : (0 : R) + 0 = 0 := by grind
        rw [hzero]
    _ =
      (xs.filter p).foldl (fun acc x => acc + f x) 0 +
        (xs.filter fun x => !p x).foldl (fun acc x => acc + f x) 0 := by
      exact foldl_sum_filter_split_start xs p f 0 0

private theorem foldl_det_sum_map {R : Type u} [Zero R] [Add R]
    {β : Type v} {γ : Type w} (xs : List β) (map : β → γ) (f : γ → R) :
    (xs.map map).foldl (fun acc x => acc + f x) 0 =
      xs.foldl (fun acc x => acc + f (map x)) 0 := by
  simp [List.foldl_map]

private theorem rowSwap_rowAddDuplicate_eq {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (_h : src ≠ dst) :
    rowSwap (rowAddDuplicate M src dst) src dst = rowAddDuplicate M src dst := by
  ext r hr k hk
  change
    (rowSwap (rowAddDuplicate M src dst) src dst)[(⟨r, hr⟩ : Fin n)][(⟨k, hk⟩ : Fin n)] =
      (rowAddDuplicate M src dst)[(⟨r, hr⟩ : Fin n)][(⟨k, hk⟩ : Fin n)]
  rw [rowSwap_get]
  let fr : Fin n := ⟨r, hr⟩
  let fk : Fin n := ⟨k, hk⟩
  change
    (if fr = dst then (rowAddDuplicate M src dst)[src][fk]
      else if fr = src then (rowAddDuplicate M src dst)[dst][fk]
      else (rowAddDuplicate M src dst)[fr][fk]) =
      (rowAddDuplicate M src dst)[fr][fk]
  by_cases hrd : fr = dst
  · rw [if_pos hrd]
    rw [rowAddDuplicate_get M src dst src fk, rowAddDuplicate_get M src dst fr fk]
    simp [hrd]
  · by_cases hrs : fr = src
    · rw [if_neg hrd, if_pos hrs]
      rw [rowAddDuplicate_get M src dst dst fk, rowAddDuplicate_get M src dst fr fk]
      simp [hrs]
    · simp [hrd, hrs]

private theorem detProduct_rowAddDuplicate_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (perm : Vector (Fin n) n) :
    detProduct (rowAddDuplicate M src dst) perm =
      detProduct (rowAddDuplicate M src dst)
        (transposePermutationValues perm src dst) := by
  have hswap :=
    detProduct_rowSwap_transposeValues
      (rowAddDuplicate M src dst) src dst h perm
  rw [rowSwap_rowAddDuplicate_eq M src dst h] at hswap
  exact hswap

private theorem detTerm_rowAddDuplicate_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (rowAddDuplicate M src dst) perm =
      -detTerm (rowAddDuplicate M src dst)
        (transposePermutationValues perm src dst) := by
  unfold detTerm
  rw [detProduct_rowAddDuplicate_transposeValues M src dst h perm,
    detSign_transposeValues (R := R) perm src dst hnodup h]
  grind

private theorem permutationVectors_duplicateRow_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAddDuplicate M src dst) perm) 0 = 0 := by
  let p : Vector (Fin n) n → Bool := fun perm => perm[src] < perm[dst]
  let term : Vector (Fin n) n → R := detTerm (rowAddDuplicate M src dst)
  have hsplit :=
    foldl_sum_filter_split (R := R) (permutationVectors n) p term
  rw [hsplit]
  have hright :
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        ((permutationVectors n).filter p).foldl
          (fun acc perm =>
            acc + term (transposePermutationValues perm src dst)) 0 := by
    have hperm :
        (((permutationVectors n).filter p).map
            fun perm => transposePermutationValues perm src dst).Perm
          ((permutationVectors n).filter fun perm => !p perm) := by
      have hleftNodup :
          (((permutationVectors n).filter p).map
              fun perm => transposePermutationValues perm src dst).Nodup := by
        exact list_nodup_map_of_injective
          (f := fun perm => transposePermutationValues perm src dst)
          (fun a b hab => by
            have h' := congrArg (fun perm => transposePermutationValues perm src dst) hab
            change
              transposePermutationValues (transposePermutationValues a src dst) src dst =
                transposePermutationValues (transposePermutationValues b src dst) src dst at h'
            rw [transposePermutationValues_involutive] at h'
            rw [transposePermutationValues_involutive] at h'
            exact h')
          (permutationVectors_nodup_list.filter p)
      have hrightNodup :
          ((permutationVectors n).filter fun perm => !p perm).Nodup :=
        permutationVectors_nodup_list.filter _
      apply (List.perm_ext_iff_of_nodup hleftNodup hrightNodup).mpr
      intro perm
      constructor
      · intro hmem
        simp only [List.mem_map, List.mem_filter] at hmem ⊢
        rcases hmem with ⟨pre, ⟨hpreMem, hpreP⟩, rfl⟩
        constructor
        · exact transposePermutationValues_mem_permutationVectors src dst hpreMem
        · have hsrc : (transposePermutationValues pre src dst)[src] = pre[dst] := by
            rw [transposePermutationValues_get]
            exact vector_get_fin_congr pre (finTranspose_left src dst)
          have hdst : (transposePermutationValues pre src dst)[dst] = pre[src] := by
            rw [transposePermutationValues_get]
            exact vector_get_fin_congr pre (finTranspose_right src dst)
          simp [p] at hpreP ⊢
          calc
            (transposePermutationValues pre src dst)[dst] = pre[src] := hdst
            _ ≤ pre[dst] := by
              change pre[src].val ≤ pre[dst].val
              have hpreP' : pre[src].val < pre[dst].val := hpreP
              omega
            _ = (transposePermutationValues pre src dst)[src] := hsrc.symm
      · intro hmem
        simp only [List.mem_filter] at hmem
        rcases hmem with ⟨hpermMem, hpfalse⟩
        simp only [List.mem_map, List.mem_filter]
        refine ⟨transposePermutationValues perm src dst,
          ⟨transposePermutationValues_mem_permutationVectors src dst hpermMem, ?_⟩, ?_⟩
        · have hsrc : (transposePermutationValues perm src dst)[src] = perm[dst] := by
            rw [transposePermutationValues_get]
            exact vector_get_fin_congr perm (finTranspose_left src dst)
          have hdst : (transposePermutationValues perm src dst)[dst] = perm[src] := by
            rw [transposePermutationValues_get]
            exact vector_get_fin_congr perm (finTranspose_right src dst)
          simp [p] at hpfalse
          have hne_values : perm[src] ≠ perm[dst] := by
            intro hvals
            have hnodup := permutationVectors_nodup hpermMem
            have hsrcidx : perm.toList.idxOf perm[src] = src.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem src.val (by simp [Vector.length_toList])
            have hdstidx : perm.toList.idxOf perm[dst] = dst.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem dst.val (by simp [Vector.length_toList])
            have hvals_idx : perm.toList.idxOf perm[src] = perm.toList.idxOf perm[dst] := by
              rw [hvals]
            have hvaleq : src.val = dst.val := by
              rw [← hsrcidx, ← hdstidx]
              exact hvals_idx
            exact h (Fin.ext hvaleq)
          rw [show p (transposePermutationValues perm src dst) =
              decide ((transposePermutationValues perm src dst)[src] <
                (transposePermutationValues perm src dst)[dst]) by rfl]
          exact decide_eq_true (by
            rw [hsrc, hdst]
            change perm[dst].val < perm[src].val
            have hle : perm[dst].val ≤ perm[src].val := hpfalse
            have hneVal : perm[dst].val ≠ perm[src].val := by
              intro hval
              exact hne_values.symm (Fin.ext hval)
            omega)
        · exact transposePermutationValues_involutive perm src dst
    calc
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        (((permutationVectors n).filter p).map
            fun perm => transposePermutationValues perm src dst).foldl
          (fun acc perm => acc + term perm) 0 := by
          exact (List.foldl_add_perm term hperm 0).symm
      _ =
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (transposePermutationValues perm src dst)) 0 := by
          exact foldl_det_sum_map ((permutationVectors n).filter p)
            (fun perm => transposePermutationValues perm src dst) term
  rw [hright]
  calc
    ((permutationVectors n).filter p).foldl (fun acc perm => acc + term perm) 0 +
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (transposePermutationValues perm src dst)) 0 =
      ((permutationVectors n).filter p).foldl
          (fun acc perm =>
            acc + (term perm + term (transposePermutationValues perm src dst))) 0 := by
        exact (List.foldl_add_add
          ((permutationVectors n).filter p) term
          (fun perm => term (transposePermutationValues perm src dst))).symm
    _ = ((permutationVectors n).filter p).foldl (fun acc _ => acc + 0) 0 := by
        apply List.foldl_add_congr
        intro perm hmem
        simp only [term]
        rw [detTerm_rowAddDuplicate_transposeValues M src dst h perm]
        · grind
        · exact permutationVectors_nodup (List.mem_filter.mp hmem).1
    _ = 0 := by
        exact List.foldl_add_zero ((permutationVectors n).filter p) 0

private theorem permutationVectors_duplicateCol_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst]) :
    (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 = 0 := by
  let p : Vector (Fin n) n → Bool :=
    fun perm => perm.toList.idxOf src < perm.toList.idxOf dst
  let term : Vector (Fin n) n → R := detTerm M
  have hsplit :=
    foldl_sum_filter_split (R := R) (permutationVectors n) p term
  rw [hsplit]
  have hright :
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (swapPermutationValues perm src dst)) 0 := by
    have hperm :
        (((permutationVectors n).filter p).map
            fun perm => swapPermutationValues perm src dst).Perm
          ((permutationVectors n).filter fun perm => !p perm) := by
      have hleftNodup :
          (((permutationVectors n).filter p).map
              fun perm => swapPermutationValues perm src dst).Nodup := by
        exact list_nodup_map_of_injective
          (f := fun perm => swapPermutationValues perm src dst)
          (fun a b hab => by
            have h' := congrArg (fun perm => swapPermutationValues perm src dst) hab
            change
              swapPermutationValues (swapPermutationValues a src dst) src dst =
                swapPermutationValues (swapPermutationValues b src dst) src dst at h'
            rw [swapPermutationValues_involutive] at h'
            rw [swapPermutationValues_involutive] at h'
            exact h')
          (permutationVectors_nodup_list.filter p)
      have hrightNodup :
          ((permutationVectors n).filter fun perm => !p perm).Nodup :=
        permutationVectors_nodup_list.filter _
      apply (List.perm_ext_iff_of_nodup hleftNodup hrightNodup).mpr
      intro perm
      constructor
      · intro hmem
        simp only [List.mem_map, List.mem_filter] at hmem ⊢
        rcases hmem with ⟨pre, ⟨hpreMem, hpreP⟩, rfl⟩
        constructor
        · exact swapPermutationValues_mem_permutationVectors src dst hpreMem
        · have hpreNodup := permutationVectors_nodup hpreMem
          simp [p] at hpreP ⊢
          rw [swapPermutationValues_idxOf_left pre src dst hpreNodup,
            swapPermutationValues_idxOf_right pre src dst hpreNodup]
          omega
      · intro hmem
        simp only [List.mem_filter] at hmem
        rcases hmem with ⟨hpermMem, hpfalse⟩
        simp only [List.mem_map, List.mem_filter]
        refine ⟨swapPermutationValues perm src dst,
          ⟨swapPermutationValues_mem_permutationVectors src dst hpermMem, ?_⟩, ?_⟩
        · have hpermNodup := permutationVectors_nodup hpermMem
          simp [p] at hpfalse ⊢
          rw [swapPermutationValues_idxOf_left perm src dst hpermNodup,
            swapPermutationValues_idxOf_right perm src dst hpermNodup]
          have hneIdx := permutation_idxOf_ne perm src dst hpermNodup h
          omega
        · exact swapPermutationValues_involutive perm src dst
    calc
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        (((permutationVectors n).filter p).map
            fun perm => swapPermutationValues perm src dst).foldl
          (fun acc perm => acc + term perm) 0 := by
          exact (List.foldl_add_perm term hperm 0).symm
      _ =
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (swapPermutationValues perm src dst)) 0 := by
          exact foldl_det_sum_map ((permutationVectors n).filter p)
            (fun perm => swapPermutationValues perm src dst) term
  rw [hright]
  calc
    ((permutationVectors n).filter p).foldl (fun acc perm => acc + term perm) 0 +
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (swapPermutationValues perm src dst)) 0 =
      ((permutationVectors n).filter p).foldl
          (fun acc perm =>
            acc + (term perm + term (swapPermutationValues perm src dst))) 0 := by
        exact (List.foldl_add_add
          ((permutationVectors n).filter p) term
          (fun perm => term (swapPermutationValues perm src dst))).symm
    _ = ((permutationVectors n).filter p).foldl (fun acc _ => acc + 0) 0 := by
        apply List.foldl_add_congr
        intro perm hmem
        simp only [term]
        rw [detTerm_colDuplicate_swapValues M src dst h hcol perm]
        · grind
        · exact permutationVectors_nodup (List.mem_filter.mp hmem).1
    _ = 0 := by
        exact List.foldl_add_zero ((permutationVectors n).filter p) 0

/-- The multilinear expansion of a column addition has zero total
duplicate-column contribution, so the Leibniz sum is unchanged. -/
private theorem permutationVectors_colAdd_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (colAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (colAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm =>
          acc + (detTerm M perm + c * detTerm (colAddDuplicate M src dst) perm)) 0 := by
        apply List.foldl_add_congr
        intro perm hmem
        exact detTerm_colAdd M src dst c perm (permutationVectors_nodup hmem)
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        (permutationVectors n).foldl
          (fun acc perm => acc + c * detTerm (colAddDuplicate M src dst) perm) 0 := by
        exact List.foldl_add_add
          (permutationVectors n) (detTerm M)
          (fun perm => c * detTerm (colAddDuplicate M src dst) perm)
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        c * (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (colAddDuplicate M src dst) perm) 0 := by
        rw [List.foldl_add_mul_left_zero]
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
        rw [permutationVectors_duplicateCol_sum (colAddDuplicate M src dst) src dst h]
        · grind
        · intro r
          rw [colAddDuplicate_get, colAddDuplicate_get]
          simp

/-- The multilinear expansion of a row addition has zero total duplicate-row
contribution, so the Leibniz sum is unchanged. -/
private theorem permutationVectors_rowAdd_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm =>
          acc + (detTerm M perm + c * detTerm (rowAddDuplicate M src dst) perm)) 0 := by
        apply List.foldl_add_congr
        intro perm _hmem
        exact detTerm_rowAdd M src dst c perm
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        (permutationVectors n).foldl
          (fun acc perm => acc + c * detTerm (rowAddDuplicate M src dst) perm) 0 := by
        exact List.foldl_add_add
          (permutationVectors n) (detTerm M) (fun perm => c * detTerm (rowAddDuplicate M src dst) perm)
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        c * (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (rowAddDuplicate M src dst) perm) 0 := by
        rw [List.foldl_add_mul_left_zero]
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
        rw [permutationVectors_duplicateRow_sum M src dst h]
        grind

/-- The Leibniz sum for the identity matrix has exactly the identity
permutation as its nonzero contribution. -/
private theorem det_identity_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat} :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (Matrix.identity (R := R) n) perm) 0 = 1 := by
  exact permutationVectors_identity_sum

/-- Swapping two rows pairs each Leibniz summand with the corresponding
transposed permutation and flips the computed inversion parity. -/
private theorem det_rowSwap_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowSwap M i j) perm) 0 =
      -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  exact permutationVectors_rowSwap_sum M i j h

/-- Scaling one row factors the scalar out of every nonzero Leibniz summand. -/
private theorem det_rowScale_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowScale M i c) perm) 0 =
      c * ((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowScale M i c) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + c * detTerm M perm) 0 := by
        apply List.foldl_add_congr
        intro perm _hmem
        exact detTerm_rowScale M i c perm
    _ = c * ((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        exact List.foldl_add_mul_left_zero (permutationVectors n) c (detTerm M)

/-- Adding a multiple of one row to a distinct row leaves the Leibniz sum
unchanged; the extra multilinear contribution has two equal rows. -/
private theorem det_rowAdd_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
  exact permutationVectors_rowAdd_sum M src dst c h

/-- The determinant of the identity matrix is one. -/
@[grind =]
theorem det_identity {R : Type u} [Lean.Grind.CommRing R] {n : Nat} :
    det (Matrix.identity (R := R) n) = 1 := by
  simpa [det] using (det_identity_leibniz (R := R) (n := n))

/-- Swapping two distinct rows negates the determinant. -/
@[grind =]
theorem det_rowSwap {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    det (rowSwap M i j) = -det M := by
  simpa [det] using det_rowSwap_leibniz M i j h

/-- Scaling a row by `c` scales the determinant by `c`. -/
@[grind =]
theorem det_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) :
    det (rowScale M i c) = c * det M := by
  simpa [det] using det_rowScale_leibniz M i c

/-- Adding a multiple of one row to a distinct row preserves the determinant. -/
@[grind =]
theorem det_rowAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    det (rowAdd M src dst c) = det M := by
  simpa [det] using det_rowAdd_leibniz M src dst c h

/-- The determinant is invariant under matrix transpose. -/
theorem det_transpose {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) :
    det M.transpose = det M := by
  unfold det
  calc
    (permutationVectors n).foldl (fun acc perm => acc + detTerm M.transpose perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + detTerm M (inversePermutationVector perm)) 0 := by
        apply List.foldl_add_congr
        intro perm hmem
        have hnodup := permutationVectors_nodup hmem
        rw [inversePermutationVector_eq perm hnodup]
        unfold detTerm
        rw [detProduct_transpose_inversePermutationValues M perm hnodup,
          ← detSign_inversePermutationValues (R := R) perm hnodup]
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
        exact permutationVectors_inverseVector_sum (R := R) (n := n) (fun perm => detTerm M perm)

/-- Cofactors commute with transpose after swapping the row and column
indices. -/
theorem cofactor_transpose {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row col : Fin (n + 1)) :
    cofactor M.transpose row col = cofactor M col row := by
  unfold cofactor
  have hsign :
      cofactorSign (R := R) row col = cofactorSign (R := R) col row := by
    unfold cofactorSign
    have hsum : row.val + col.val = col.val + row.val := Nat.add_comm _ _
    rw [hsum]
  rw [hsign, deleteRowCol_transpose, det_transpose]

/-- Permuting columns multiplies the determinant by the sign of the column permutation. -/
theorem det_colPermute_vector {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (sigma : Vector (Fin n) n)
    (hsigma : sigma ∈ permutationVectors n) :
    det ((ofFn fun r c => M[r][sigma[c]]) : Matrix R n n) =
      detSign (R := R) sigma * det M := by
  unfold det
  calc
    (permutationVectors n).foldl
        (fun acc tau =>
          acc + detTerm ((ofFn fun r c => M[r][sigma[c]]) : Matrix R n n) tau) 0 =
      (permutationVectors n).foldl
        (fun acc tau =>
          acc + detSign (R := R) sigma *
            detTerm M (composePermutationValues sigma tau)) 0 := by
        apply List.foldl_add_congr
        intro tau htau
        unfold detTerm
        rw [detProduct_colPermute_vector]
        rw [detSign_eq_mul_detSign_composePermutationValues
          (R := R) sigma tau hsigma htau]
        grind
    _ =
      detSign (R := R) sigma *
        (permutationVectors n).foldl
          (fun acc tau => acc + detTerm M (composePermutationValues sigma tau)) 0 := by
        exact List.foldl_add_mul_left_zero
          (permutationVectors n) (detSign (R := R) sigma)
          (fun tau => detTerm M (composePermutationValues sigma tau))
    _ =
      detSign (R := R) sigma *
        (permutationVectors n).foldl (fun acc tau => acc + detTerm M tau) 0 := by
        rw [permutationVectors_composePermutationValues_left_sum
          (R := R) sigma hsigma (fun tau => detTerm M tau)]

/-- Swapping two columns negates determinant. -/
theorem det_colSwap {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    det (ofFn fun r c => M[r][finTranspose i j c]) = -det M := by
  let C : Matrix R n n := ofFn fun r c => M[r][finTranspose i j c]
  have htranspose : C.transpose = rowSwap M.transpose i j := by
    ext r hr c hc
    let rr : Fin n := ⟨r, hr⟩
    let cc : Fin n := ⟨c, hc⟩
    change C.transpose[rr][cc] = (rowSwap M.transpose i j)[rr][cc]
    rw [rowSwap_get_finTranspose M.transpose i j rr h cc,
      show C.transpose[rr][cc] = C[cc][rr] by simp [Matrix.transpose, Matrix.col],
      show C[cc][rr] = M[cc][finTranspose i j rr] by simp [C, ofFn]]
    simp [Matrix.transpose, Matrix.col]
  calc
    det C = det C.transpose := (det_transpose C).symm
    _ = det (rowSwap M.transpose i j) := by rw [htranspose]
    _ = -det M.transpose := det_rowSwap M.transpose i j h
    _ = -det M := by rw [det_transpose M]

/-- Adding a multiple of one column to a distinct column preserves determinant. -/
theorem det_colAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    det (colAdd M src dst c) = det M := by
  simpa [det] using permutationVectors_colAdd_sum M src dst c h

end Matrix
end Hex
