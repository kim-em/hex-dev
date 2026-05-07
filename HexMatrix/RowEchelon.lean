import HexMatrix.Basic
import Batteries.Data.List.Lemmas
import Batteries.Data.List.Pairwise
import Batteries.Data.List.Perm

/-!
Row operations and echelon-form data for `hex-matrix`.

This module adds executable row-operation helpers together with the pure data
structures and contracts used by later row-reduction, span/nullspace, and
determinant routines.
-/

namespace Hex

universe u

namespace Matrix

/-- Swap rows `i` and `j` in a dense matrix. -/
def rowSwap (M : Matrix R n m) (i j : Fin n) : Matrix R n m :=
  (M.set i M[j]).set j M[i]

/-- Read an entry of `rowSwap M i j` by cases on the row index: row `j`
returns the original row `i`, row `i` returns the original row `j`, and any
other row is unchanged. -/
theorem rowSwap_getElem (M : Matrix R n m) (i j r : Fin n) (k : Fin m) :
    (rowSwap M i j)[r][k] =
      if r = j then M[i][k] else if r = i then M[j][k] else M[r][k] := by
  by_cases hrj : r = j
  · subst r
    simp [rowSwap]
  · by_cases hri : r = i
    · subst r
      simp [rowSwap, hrj]
      have hval : j.val ≠ i.val := by
        intro hval
        exact hrj (Fin.ext hval.symm)
      have hrow : ((M.set i M[j]).set j M[i])[i] = (M.set i M[j])[i] := by
        exact Vector.getElem_set_ne (xs := M.set i M[j]) (x := M[i])
          j.isLt i.isLt hval
      simpa using congrArg (fun row => row[k]) hrow
    · simp [rowSwap, hrj, hri]
      have hir : i.val ≠ r.val := by
        intro hval
        exact hri (Fin.ext hval.symm)
      have hjr : j.val ≠ r.val := by
        intro hval
        exact hrj (Fin.ext hval.symm)
      have hrow₁ : (M.set i M[j])[r] = M[r] := by
        exact Vector.getElem_set_ne (xs := M) (x := M[j]) i.isLt r.isLt hir
      have hrow₂ : ((M.set i M[j]).set j M[i])[r] = (M.set i M[j])[r] := by
        exact Vector.getElem_set_ne (xs := M.set i M[j]) (x := M[i])
          j.isLt r.isLt hjr
      exact (congrArg (fun row => row[k]) hrow₂).trans
        (congrArg (fun row => row[k]) hrow₁)

/-- Diagonal-entry corollary of `rowSwap_getElem` for square matrices: when
`pivot ≠ k`, the `(k, k)` entry of `rowSwap M k pivot` is the original
`(pivot, k)` entry. Used by Bareiss row-pivoted invariants to fold a row swap
into a single matrix lookup without unfolding `Vector.set`. -/
theorem rowSwap_diag_of_ne (M : Matrix R n n) {k pivot : Fin n}
    (h : pivot ≠ k) :
    (rowSwap M k pivot)[k][k] = M[pivot][k] := by
  rw [rowSwap_getElem]
  by_cases hkp : k = pivot
  · exact (h hkp.symm).elim
  · simp [hkp]

/-- Scale row `i` by `c`. -/
def rowScale [Mul R] (M : Matrix R n m) (i : Fin n) (c : R) : Matrix R n m :=
  M.set i <| Vector.ofFn fun k => c * M[i][k]

/-- Replace row `dst` by `row dst + c * row src`. -/
def rowAdd [Mul R] [Add R] (M : Matrix R n m) (src dst : Fin n) (c : R) : Matrix R n m :=
  M.set dst <| Vector.ofFn fun k => M[dst][k] + c * M[src][k]

/-- Replace column `dst` by `col dst + c * col src`. -/
def colAdd [Mul R] [Add R] (M : Matrix R n m) (src dst : Fin m) (c : R) : Matrix R n m :=
  Matrix.ofFn fun i j => if j = dst then M[i][j] + c * M[i][src] else M[i][j]

/-- Pure data produced by an echelon-form algorithm. -/
structure RowEchelonData (R : Type u) (n m : Nat) where
  rank : Nat
  echelon : Matrix R n m
  transform : Matrix R n n
  pivotCols : Vector (Fin m) rank

/-- Shared conditions for any echelon form. -/
structure IsEchelonForm [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    (M : Matrix R n m) (D : RowEchelonData R n m) : Prop where
  transform_mul : D.transform * M = D.echelon
  transform_inv : ∃ Tinv : Matrix R n n, Tinv * D.transform = 1
  transform_right_inv : ∃ Tinv : Matrix R n n, D.transform * Tinv = 1
  rank_le_n : D.rank ≤ n
  rank_le_m : D.rank ≤ m
  pivotCols_sorted : ∀ i j, i < j → D.pivotCols.get i < D.pivotCols.get j
  below_pivot_zero : ∀ (i : Fin D.rank) (j : Fin n),
      i.val < j.val → D.echelon[j][D.pivotCols.get i] = 0
  zero_row : ∀ (i : Fin n), D.rank ≤ i.val → D.echelon[i] = 0

/-- RREF-specific conditions on top of `IsEchelonForm`. -/
structure IsRREF [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    (M : Matrix R n m) (D : RowEchelonData R n m)
    : Prop extends IsEchelonForm M D where
  pivot_one : ∀ (i : Fin D.rank), D.echelon[i][D.pivotCols.get i] = 1
  above_pivot_zero : ∀ (i : Fin D.rank) (j : Fin n),
      j.val < i.val → D.echelon[j][D.pivotCols.get i] = 0

namespace IsEchelonForm

variable [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
variable {M : Matrix R n m} {D : RowEchelonData R n m}

/-- The square row-transform has a right inverse. -/
theorem transform_mul_inv (E : IsEchelonForm M D) :
    ∃ Tinv : Matrix R n n, D.transform * Tinv = 1 := by
  exact E.transform_right_inv

private theorem pivotCols_pairwise (E : IsEchelonForm M D) :
    List.Pairwise (fun a b : Fin m => a < b) D.pivotCols.toList := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < D.rank := by simpa [Vector.length_toList] using hi
  have hj' : j < D.rank := by simpa [Vector.length_toList] using hj
  have h := E.pivotCols_sorted ⟨i, hi'⟩ ⟨j, hj'⟩ hij
  simpa [Vector.getElem_toList] using h

private theorem pivotCols_nodup (E : IsEchelonForm M D) :
    D.pivotCols.toList.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact E.pivotCols_pairwise.imp (fun hlt heq => by subst heq; omega)

/-- The pivot columns are injective because they are strictly increasing. -/
theorem pivotCols_injective (E : IsEchelonForm M D) :
    Function.Injective fun i : Fin D.rank => D.pivotCols.get i := by
  intro i j h
  by_cases hne : i = j
  · exact hne
  have hval : i.val ≠ j.val := by
    intro hval
    exact hne (Fin.ext hval)
  cases Nat.lt_or_gt_of_ne hval with
  | inl hij =>
      have hp := E.pivotCols_sorted i j hij
      have h' : D.pivotCols.get i = D.pivotCols.get j := h
      rw [h'] at hp
      exact False.elim (by omega)
  | inr hji =>
      have hp := E.pivotCols_sorted j i hji
      have h' : D.pivotCols.get i = D.pivotCols.get j := h
      rw [h'] at hp
      exact False.elim (by omega)

/-- The non-pivot columns, enumerated in increasing order. -/
def freeColsList (_E : IsEchelonForm M D) : List (Fin m) :=
  (List.finRange m).filter fun j => j ∉ D.pivotCols.toList

theorem freeColsList_length (E : IsEchelonForm M D) :
    E.freeColsList.length = m - D.rank := by
  let p : Fin m → Bool := fun j => decide (j ∈ D.pivotCols.toList)
  have hpivotFilterLen : ((List.finRange m).filter p).length = D.rank := by
    have hfilterPairs : List.Pairwise (fun a b : Fin m => a < b)
        ((List.finRange m).filter p) := by
      exact List.Pairwise.filter p (List.pairwise_lt_finRange m)
    have hfilterNodup : ((List.finRange m).filter p).Nodup := by
      rw [List.nodup_iff_pairwise_ne]
      exact hfilterPairs.imp (fun hlt heq => by subst heq; omega)
    have hperm : D.pivotCols.toList.Perm ((List.finRange m).filter p) := by
      rw [List.perm_ext_iff_of_nodup E.pivotCols_nodup hfilterNodup]
      intro a
      constructor
      · intro ha
        rw [List.mem_filter]
        exact ⟨List.mem_finRange a, show p a = true from by exact decide_eq_true ha⟩
      · intro ha
        rw [List.mem_filter] at ha
        exact of_decide_eq_true ha.2
    have hlen := hperm.length_eq
    simpa [p, Vector.length_toList] using hlen.symm
  have hsum : ((List.finRange m).filter p).length + E.freeColsList.length = m := by
    have hlen := (List.filter_append_perm p (List.finRange m)).length_eq
    simpa [p, freeColsList, List.length_finRange] using hlen
  omega

/-- Sorted complement of the pivot columns. -/
def freeCols (E : IsEchelonForm M D) : Vector (Fin m) (m - D.rank) :=
  ⟨E.freeColsList.toArray, by simpa using E.freeColsList_length⟩

private theorem freeCols_get_eq (E : IsEchelonForm M D) (i : Fin (m - D.rank)) :
    E.freeCols.get i =
      E.freeColsList[i.val]'(by rw [freeColsList_length]; exact i.isLt) := by
  unfold freeCols
  simp [Vector.get, List.getElem_toArray]

private theorem freeColsList_pairwise (E : IsEchelonForm M D) :
    List.Pairwise (fun a b : Fin m => a < b) E.freeColsList := by
  unfold freeColsList
  exact List.Pairwise.filter (fun j => j ∉ D.pivotCols.toList) (List.pairwise_lt_finRange m)

theorem freeCols_sorted (E : IsEchelonForm M D) :
    ∀ i j, i < j → E.freeCols.get i < E.freeCols.get j := by
  intro i j hij
  have hpair := E.freeColsList_pairwise
  rw [List.pairwise_iff_getElem] at hpair
  have hi : i.val < E.freeColsList.length := by
    rw [freeColsList_length]
    exact i.isLt
  have hj : j.val < E.freeColsList.length := by
    rw [freeColsList_length]
    exact j.isLt
  simpa [E.freeCols_get_eq i, E.freeCols_get_eq j] using hpair i.val j.val hi hj hij

/-- The free columns are injective because they are strictly increasing. -/
theorem freeCols_injective (E : IsEchelonForm M D) :
    Function.Injective fun i : Fin (m - D.rank) => E.freeCols.get i := by
  intro i j h
  by_cases hne : i = j
  · exact hne
  have hval : i.val ≠ j.val := by
    intro hval
    exact hne (Fin.ext hval)
  cases Nat.lt_or_gt_of_ne hval with
  | inl hij =>
      have hp := E.freeCols_sorted i j hij
      have h' : E.freeCols.get i = E.freeCols.get j := h
      rw [h'] at hp
      exact False.elim (by omega)
  | inr hji =>
      have hp := E.freeCols_sorted j i hji
      have h' : E.freeCols.get i = E.freeCols.get j := h
      rw [h'] at hp
      exact False.elim (by omega)

/-- Every column is either a pivot column or a free column. -/
theorem colPartition (E : IsEchelonForm M D) (j : Fin m) :
    (∃ i : Fin D.rank, D.pivotCols.get i = j) ∨
    (∃ k : Fin (m - D.rank), E.freeCols.get k = j) := by
  by_cases hp : j ∈ D.pivotCols.toList
  · left
    rw [List.mem_iff_getElem] at hp
    rcases hp with ⟨i, hi, hget⟩
    have hi' : i < D.rank := by simpa [Vector.length_toList] using hi
    exact ⟨⟨i, hi'⟩, by simpa [Vector.getElem_toList] using hget⟩
  · right
    have hfreeMem : j ∈ E.freeColsList := by
      unfold freeColsList
      rw [List.mem_filter]
      exact ⟨List.mem_finRange j, by simpa using decide_eq_true hp⟩
    rw [List.mem_iff_getElem] at hfreeMem
    rcases hfreeMem with ⟨k, hk, hget⟩
    have hk' : k < m - D.rank := by simpa [freeColsList_length] using hk
    refine ⟨⟨k, hk'⟩, ?_⟩
    simpa [E.freeCols_get_eq ⟨k, hk'⟩] using hget

theorem colPartition_exclusive (E : IsEchelonForm M D) (j : Fin m) :
    ¬((∃ i : Fin D.rank, D.pivotCols.get i = j) ∧
      (∃ k : Fin (m - D.rank), E.freeCols.get k = j)) := by
  rintro ⟨⟨i, hpivot⟩, ⟨k, hfree⟩⟩
  have hpivotMem : j ∈ D.pivotCols.toList := by
    rw [List.mem_iff_getElem]
    refine ⟨i.val, by simp [Vector.length_toList], ?_⟩
    simpa [Vector.getElem_toList, hpivot]
  have hfreeMem : j ∈ E.freeColsList := by
    rw [List.mem_iff_getElem]
    refine ⟨k.val, by rw [freeColsList_length]; exact k.isLt, ?_⟩
    simpa [E.freeCols_get_eq k, hfree]
  unfold freeColsList at hfreeMem
  rw [List.mem_filter] at hfreeMem
  exact (of_decide_eq_true hfreeMem.2) hpivotMem

/-- No column can be both pivot and free. -/
theorem pivotCols_disjoint_freeCols (E : IsEchelonForm M D) :
    ∀ (i : Fin D.rank) (k : Fin (m - D.rank)),
      D.pivotCols.get i ≠ E.freeCols.get k := by
  intro i k h
  exact E.colPartition_exclusive (D.pivotCols.get i)
    ⟨⟨i, rfl⟩, ⟨k, h.symm⟩⟩

end IsEchelonForm

end Matrix
end Hex
