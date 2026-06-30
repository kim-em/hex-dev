/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduce.Span
import all HexRowReduce.Span

public section

/-!
Nullspace API over the reduced-row-echelon contract.

From the free columns of an `IsRowReduced` form this constructs the nullspace
basis (`nullspaceMatrix`, `nullspace`) and proves it both sound
(`nullspace_sound`: each basis vector is killed by `M`) and complete
(`nullspace_complete`: every nullspace vector is a combination of the basis).
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n m : Nat}

namespace IsRowReduced

variable {M : Matrix R n m} {D : RowEchelonData R n m}

variable [Mul R] [Add R] [OfNat R 0] [OfNat R 1]

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
def pivotIndex? (D : RowEchelonData R n m) (j : Fin m) : Option (Fin D.rank) :=
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
@[expose]
def nullspaceMatrix [Lean.Grind.Ring R] (E : IsRowReduced M D) :
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

/-- In the `k`th nullspace-matrix column, the row for its own free column is `1`. -/
@[grind =] theorem nullspaceMatrix_free [Lean.Grind.Ring R] (E : IsRowReduced M D)
    (k : Fin (m - D.rank)) :
    E.nullspaceMatrix[E.toIsEchelonForm.freeCols.get k][k] = 1 := by
  unfold nullspaceMatrix Matrix.ofFn
  simp

/-- In the `k`th nullspace-matrix column, every other free-column row is `0`. -/
@[grind =] theorem nullspaceMatrix_free_ne [Lean.Grind.Ring R] (E : IsRowReduced M D)
    {k l : Fin (m - D.rank)} (hkl : k ≠ l) :
    E.nullspaceMatrix[E.toIsEchelonForm.freeCols.get l][k] = 0 := by
  unfold nullspaceMatrix Matrix.ofFn
  have hne : E.toIsEchelonForm.freeCols.get l ≠ E.toIsEchelonForm.freeCols.get k := by
    intro h
    exact hkl ((E.toIsEchelonForm.freeCols_injective h).symm)
  simp [hne, pivotIndex?_free_none E.toIsEchelonForm l]

/-- In a pivot-column row, a nullspace-matrix entry is the negative RREF entry in
the matching pivot row and free column. -/
@[grind =] theorem nullspaceMatrix_pivot [Lean.Grind.Ring R] (E : IsRowReduced M D)
    (i : Fin D.rank) (k : Fin (m - D.rank)) :
    E.nullspaceMatrix[D.pivotCols.get i][k] =
      -(D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm i)][E.toIsEchelonForm.freeCols.get k]) := by
  unfold nullspaceMatrix Matrix.ofFn
  simp [E.toIsEchelonForm.pivotCols_disjoint_freeCols i k,
    pivotIndex?_pivot E.toIsEchelonForm i]

/-- The individual nullspace basis vectors. -/
@[expose]
def nullspace [Lean.Grind.Ring R] (E : IsRowReduced M D) :
    Vector (Vector R m) (m - D.rank) :=
  Vector.ofFn fun k => Matrix.col (E.nullspaceMatrix) k

private theorem nullspace_get [Lean.Grind.Ring R] (E : IsRowReduced M D)
    (k : Fin (m - D.rank)) :
    E.nullspace.get k = Matrix.col E.nullspaceMatrix k := by
  unfold nullspace
  exact Vector.getElem_ofFn _

/-- On its own free column, a nullspace basis vector has entry `1`. -/
@[grind =] theorem nullspace_get_free [Lean.Grind.Ring R] (E : IsRowReduced M D)
    (k : Fin (m - D.rank)) :
    (E.nullspace.get k)[E.toIsEchelonForm.freeCols.get k] = 1 := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_free E k

/-- On every other free column, a nullspace basis vector has entry `0`. -/
@[grind =] theorem nullspace_get_free_ne [Lean.Grind.Ring R] (E : IsRowReduced M D)
    {k l : Fin (m - D.rank)} (hkl : k ≠ l) :
    (E.nullspace.get k)[E.toIsEchelonForm.freeCols.get l] = 0 := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_free_ne E hkl

/-- On a pivot column, a nullspace basis vector is the negative RREF entry in
the matching pivot row and free column. -/
@[grind =] theorem nullspace_get_pivot [Lean.Grind.Ring R] (E : IsRowReduced M D)
    (i : Fin D.rank) (k : Fin (m - D.rank)) :
    (E.nullspace.get k)[D.pivotCols.get i] =
      -(D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm i)][E.toIsEchelonForm.freeCols.get k]) := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_pivot E i k

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in


omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem foldl_one_nonzero {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} [DecidableEq α] (xs : List α) (a : α) (f : α → R) (x : R)
    (haMem : a ∈ xs) (hnodup : xs.Nodup)
    (ha : f a = x) (hz : ∀ z ∈ xs, z ≠ a → f z = 0) :
    xs.foldl (fun acc z => acc + f z) 0 = x := by
  induction xs with
  | nil =>
      cases haMem
  | cons z zs ih =>
      simp only [List.foldl_cons]
      by_cases hza : z = a
      · subst z
        rw [ha]
        have hzero : ∀ y ∈ zs, f y = 0 := by
          intro y hy
          have hya : y ≠ a := by
            intro h
            subst y
            exact (List.nodup_cons.mp hnodup).1 hy
          exact hz y (List.mem_cons_of_mem _ hy) hya
        have h0x : (0 : R) + x = x := by grind
        rw [h0x, List.foldl_add_eq_self zs f x hzero]
      · have hz0 : f z = 0 := hz z (by simp) hza
        rw [hz0]
        have haTail : a ∈ zs := by
          rcases List.mem_cons.mp haMem with hhead | htail
          · exact False.elim (hza hhead.symm)
          · exact htail
        have hnodupTail : zs.Nodup := (List.nodup_cons.mp hnodup).2
        have hzTail : ∀ y ∈ zs, y ≠ a → f y = 0 := by
          intro y hy hya
          exact hz y (List.mem_cons_of_mem _ hy) hya
        have hzeroAdd : (0 : R) + 0 = 0 := by grind
        rw [hzeroAdd]
        exact ih haTail hnodupTail hzTail

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem foldl_two_nonzero {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} [DecidableEq α] (xs : List α) (a b : α) (f : α → R) (x y : R)
    (hab : a ≠ b) (haMem : a ∈ xs) (hbMem : b ∈ xs) (hnodup : xs.Nodup)
    (ha : f a = x) (hb : f b = y)
    (hz : ∀ z ∈ xs, z ≠ a → z ≠ b → f z = 0) :
    xs.foldl (fun acc z => acc + f z) 0 = x + y := by
  induction xs with
  | nil =>
      cases haMem
  | cons z zs ih =>
      simp only [List.foldl_cons]
      by_cases hza : z = a
      · subst z
        rw [ha]
        have hbTail : b ∈ zs := by
          rcases List.mem_cons.mp hbMem with hhead | htail
          · exact False.elim (hab hhead.symm)
          · exact htail
        have hnodupTail : zs.Nodup := (List.nodup_cons.mp hnodup).2
        have hbOnly : ∀ t ∈ zs, t ≠ b → f t = 0 := by
          intro t ht htb
          have hta : t ≠ a := by
            intro h
            subst t
            exact (List.nodup_cons.mp hnodup).1 ht
          exact hz t (List.mem_cons_of_mem _ ht) hta htb
        have h0x : (0 : R) + x = x := by grind
        rw [h0x, List.foldl_add_eq_add_foldl zs f x, foldl_one_nonzero zs b f y hbTail hnodupTail hb hbOnly]
      · by_cases hzb : z = b
        · subst z
          rw [hb]
          have haTail : a ∈ zs := by
            rcases List.mem_cons.mp haMem with hhead | htail
            · exact False.elim (hza hhead.symm)
            · exact htail
          have hnodupTail : zs.Nodup := (List.nodup_cons.mp hnodup).2
          have haOnly : ∀ t ∈ zs, t ≠ a → f t = 0 := by
            intro t ht hta
            have htb : t ≠ b := by
              intro h
              subst t
              exact (List.nodup_cons.mp hnodup).1 ht
            exact hz t (List.mem_cons_of_mem _ ht) hta htb
          have h0y : (0 : R) + y = y := by grind
          rw [h0y, List.foldl_add_eq_add_foldl zs f y, foldl_one_nonzero zs a f x haTail hnodupTail ha haOnly]
          grind
        · have hz0 : f z = 0 := hz z (by simp) hza hzb
          rw [hz0]
          have haTail : a ∈ zs := by
            rcases List.mem_cons.mp haMem with hhead | htail
            · exact False.elim (hza hhead.symm)
            · exact htail
          have hbTail : b ∈ zs := by
            rcases List.mem_cons.mp hbMem with hhead | htail
            · exact False.elim (hzb hhead.symm)
            · exact htail
          have hnodupTail : zs.Nodup := (List.nodup_cons.mp hnodup).2
          have hzTail : ∀ t ∈ zs, t ≠ a → t ≠ b → f t = 0 := by
            intro t ht hta htb
            exact hz t (List.mem_cons_of_mem _ ht) hta htb
          have hzeroAdd : (0 : R) + 0 = 0 := by grind
          rw [hzeroAdd]
          exact ih haTail hbTail hnodupTail hzTail

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem nullspace_echelon_sound {R : Type u} [Lean.Grind.Ring R] {n m : Nat}
    {M : Matrix R n m} {D : RowEchelonData R n m} (E : IsRowReduced M D)
    (k : Fin (m - D.rank)) :
    D.echelon * E.nullspace.get k = 0 := by
  ext r hr
  let row : Fin n := ⟨r, hr⟩
  by_cases hrow : r < D.rank
  · let ri : Fin D.rank := ⟨r, hrow⟩
    let free := E.toIsEchelonForm.freeCols.get k
    let pivot := D.pivotCols.get ri
    let coeff := D.echelon[row][free]
    have hrowEq : row = E.toIsEchelonForm.pivotRow ri := by
      apply Fin.ext
      rfl
    have hpivotFree : pivot ≠ free := by
      exact E.toIsEchelonForm.pivotCols_disjoint_freeCols ri k
    change (Matrix.mulVec D.echelon (E.nullspace.get k))[r] = (0 : Vector R n)[r]
    unfold Matrix.mulVec Matrix.row Vector.dotProduct
    rw [Vector.getElem_ofFn hr, Vector.getElem_zero r hr]
    change (List.finRange m).foldl
        (fun acc j => acc + D.echelon[row][j] * (E.nullspace.get k)[j]) 0 = 0
    have hpivotTerm :
        D.echelon[row][pivot] * (E.nullspace.get k)[pivot] = -coeff := by
      have hpone : D.echelon[row][pivot] = 1 := by
        simpa [row, ri, pivot, IsEchelonForm.pivotRow] using E.pivot_one ri
      have hnp := nullspace_get_pivot E ri k
      rw [hpone, hnp]
      have hcoeff :
          D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm ri)][free] = coeff := by
        simp [free, coeff, row, ri, IsEchelonForm.pivotRow]
      change (1 : R) *
          (-D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm ri)][free]) = -coeff
      rw [hcoeff]
      grind
    have hfreeTerm :
        D.echelon[row][free] * (E.nullspace.get k)[free] = coeff := by
      have hnf := nullspace_get_free E k
      rw [hnf]
      grind
    have hzero :
        ∀ j ∈ List.finRange m, j ≠ pivot → j ≠ free →
          D.echelon[row][j] * (E.nullspace.get k)[j] = 0 := by
      intro j _ hjp hjf
      rcases E.toIsEchelonForm.colPartition j with ⟨i, hi⟩ | ⟨l, hl⟩
      · have hij : i ≠ ri := by
          intro hir
          subst i
          exact hjp hi.symm
        have hpivotZero : D.echelon[row][D.pivotCols.get i] = 0 := by
          have hval : i.val ≠ ri.val := by
            intro h
            exact hij (Fin.ext h)
          cases Nat.lt_or_gt_of_ne hval with
          | inl hlt =>
              have hbelow := E.toIsEchelonForm.below_pivot_zero i row (by
                change i.val < r
                simpa [ri] using hlt)
              simpa using hbelow
          | inr hgt =>
              have habove := E.above_pivot_zero i row (by
                change r < i.val
                simpa [ri] using hgt)
              simpa using habove
        rw [← hi, hpivotZero]
        grind
      · have hlk : k ≠ l := by
          intro hkl
          subst l
          exact hjf hl.symm
        have hfreeZero := nullspace_get_free_ne E hlk
        rw [← hl, hfreeZero]
        grind
    have hsum := foldl_two_nonzero (R := R) (xs := List.finRange m) pivot free
      (fun j => D.echelon[row][j] * (E.nullspace.get k)[j]) (-coeff) coeff
      hpivotFree (List.mem_finRange pivot) (List.mem_finRange free)
      (List.nodup_finRange m) hpivotTerm hfreeTerm hzero
    calc
      (List.finRange m).foldl
          (fun acc j => acc + D.echelon[row][j] * (E.nullspace.get k)[j]) 0 =
          -coeff + coeff := by
            simpa only using hsum
      _ = 0 := by grind
  · have hzeroRow := E.toIsEchelonForm.zero_row row (by
      exact Nat.le_of_not_gt hrow)
    change (Matrix.mulVec D.echelon (E.nullspace.get k))[r] = (0 : Vector R n)[r]
    unfold Matrix.mulVec Matrix.row Vector.dotProduct
    rw [Vector.getElem_ofFn hr, Vector.getElem_zero r hr]
    change (List.finRange m).foldl
        (fun acc j => acc + D.echelon[row][j] * (E.nullspace.get k)[j]) 0 = 0
    have hzero :
        ∀ j ∈ List.finRange m, D.echelon[row][j] * (E.nullspace.get k)[j] = 0 := by
      intro j _
      have hentry : D.echelon[row][j] = 0 := by
        have hrowGet := congrArg (fun v => v[j]) hzeroRow
        simpa using hrowGet
      rw [hentry]
      grind
    simpa only using List.foldl_add_eq_self (List.finRange m)
      (fun j => D.echelon[row][j] * (E.nullspace.get k)[j]) 0 hzero

/-- Every basis vector returned by `nullspace` lies in the nullspace of `M`. -/
theorem nullspace_sound {R : Type u} [Lean.Grind.Ring R] {n m : Nat}
    {M : Matrix R n m} {D : RowEchelonData R n m} (E : IsRowReduced M D) (k : Fin (m - D.rank)) :
    M * E.nullspace.get k = 0 := by
  let b := E.nullspace.get k
  have hbEchelon : D.echelon * b = 0 := by
    exact nullspace_echelon_sound (M := M) (D := D) E k
  have hbTransform : D.transform * (M * b) = 0 := by
    calc
      D.transform * (M * b) = (D.transform * M) * b := by
        exact (Matrix.mul_assoc_vec D.transform M b).symm
      _ = D.echelon * b := by
        rw [E.toIsEchelonForm.transform_mul]
      _ = 0 := hbEchelon
  rcases E.toIsEchelonForm.transform_inv with ⟨Tinv, hTinv⟩
  calc
    M * b = (Matrix.identity (R := R) n) * (M * b) := by
      rw [Matrix.identity_mulVec]
    _ = (Tinv * D.transform) * (M * b) := by
      rw [hTinv]
    _ = Tinv * (D.transform * (M * b)) := by
      exact Matrix.mul_assoc_vec Tinv D.transform (M * b)
    _ = Tinv * (0 : Vector R n) := by
      rw [hbTransform]
    _ = 0 := by
      rw [Matrix.mulVec_zero]

private theorem vector_toList_eq_finRange_map_get {α : Type u} {n : Nat}
    (v : Vector α n) :
    v.toList = (List.finRange n).map fun i => v[i] := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k _ _
    simp



omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem pivotCols_toList_nodup
    [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) :
    D.pivotCols.toList.Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < D.rank := by simpa [Vector.length_toList] using hi
  have hj' : j < D.rank := by simpa [Vector.length_toList] using hj
  have h := E.pivotCols_sorted ⟨i, hi'⟩ ⟨j, hj'⟩ hij
  intro heq
  have heqGet :
      D.pivotCols.toList[i]'hi = D.pivotCols.toList[j]'hj := heq
  rw [Vector.getElem_toList, Vector.getElem_toList] at heqGet
  have : D.pivotCols.get ⟨i, hi'⟩ = D.pivotCols.get ⟨j, hj'⟩ := heqGet
  rw [this] at h
  omega

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem finRange_perm_pivot_free
    [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) :
    (List.finRange m).Perm
      (D.pivotCols.toList ++ E.freeColsList) := by
  let p : Fin m → Bool := fun j => decide (j ∈ D.pivotCols.toList)
  have hpivot_pair : List.Pairwise (fun a b : Fin m => a < b)
      ((List.finRange m).filter p) :=
    List.Pairwise.filter p (List.pairwise_lt_finRange m)
  have hpivot_nodup : ((List.finRange m).filter p).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hpivot_pair.imp (fun hlt heq => by subst heq; omega)
  have hpivot_perm : D.pivotCols.toList.Perm ((List.finRange m).filter p) := by
    rw [List.perm_ext_iff_of_nodup (pivotCols_toList_nodup E) hpivot_nodup]
    intro a
    constructor
    · intro ha
      rw [List.mem_filter]
      refine ⟨List.mem_finRange a, ?_⟩
      exact decide_eq_true ha
    · intro ha
      rw [List.mem_filter] at ha
      exact of_decide_eq_true ha.2
  have hfree_eq :
      E.freeColsList = (List.finRange m).filter (fun j => !p j) := by
    unfold IsEchelonForm.freeColsList
    apply List.filter_congr
    intro j _hj
    show decide (j ∉ D.pivotCols.toList) = !decide (j ∈ D.pivotCols.toList)
    by_cases hjp : j ∈ D.pivotCols.toList
    · simp [hjp]
    · simp [hjp]
  have hgoal : (D.pivotCols.toList ++ E.freeColsList).Perm (List.finRange m) := by
    rw [hfree_eq]
    exact (hpivot_perm.append_right _).trans
      (List.filter_append_perm p (List.finRange m))
  exact hgoal.symm

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
/-- The pivot-column entry in row `pivotRow i` is `1` exactly when the pivot
indices match. This is the indicator characterization used to extract
`v[D.pivotCols.get i]` from the row sum. -/
private theorem pivot_column_entry_pivotRow {R : Type u} [Lean.Grind.Field R]
    {n m : Nat} {M : Matrix R n m} {D : RowEchelonData R n m} (E : IsRowReduced M D)
    (i i' : Fin D.rank) :
    D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i'] =
      if i' = i then (1 : R) else 0 := by
  have h := pivot_column_entry E i' (E.toIsEchelonForm.pivotRow i)
  by_cases hii : i' = i
  · subst i'
    rw [if_pos rfl, h, if_pos rfl]
  · rw [if_neg hii]
    rw [h]
    have hrow_ne : E.toIsEchelonForm.pivotRow i' ≠ E.toIsEchelonForm.pivotRow i := by
      intro heq
      apply hii
      apply Fin.ext
      simpa [IsEchelonForm.pivotRow] using congrArg Fin.val heq
    rw [if_neg hrow_ne]

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
/-- The row of `D.echelon * v` at `pivotRow i`, expanded as a foldl, is the
sum of the pivot-column contribution `v[D.pivotCols.get i]` plus the
free-column contributions. When `D.echelon * v = 0`, this gives a relation
between `v[D.pivotCols.get i]` and the free-column entries. -/
private theorem freeSum_eq_neg_pivot {R : Type u} [Lean.Grind.Field R] {n m : Nat}
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsRowReduced M D) {v : Vector R m}
    (hEchelon : D.echelon * v = 0) (i : Fin D.rank) :
    v[D.pivotCols.get i] +
      (List.finRange (m - D.rank)).foldl
        (fun acc k =>
          acc +
            D.echelon[E.toIsEchelonForm.pivotRow i][E.toIsEchelonForm.freeCols.get k] *
              v[E.toIsEchelonForm.freeCols.get k]) 0 = 0 := by
  -- Expand `(D.echelon * v)[pivotRow i] = 0` into a foldl over `Fin m`.
  have hZero : (List.finRange m).foldl
      (fun acc l =>
        acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 = 0 := by
    have hentry := congrArg (fun w => w[(E.toIsEchelonForm.pivotRow i).val]'
      (E.toIsEchelonForm.pivotRow i).isLt) hEchelon
    -- `hentry : (D.echelon * v)[pivotRow i] = (0 : Vector R n)[pivotRow i]`
    change
      (Matrix.mulVec D.echelon v)[(E.toIsEchelonForm.pivotRow i).val]'
        (E.toIsEchelonForm.pivotRow i).isLt =
      (0 : Vector R n)[(E.toIsEchelonForm.pivotRow i).val]'
        (E.toIsEchelonForm.pivotRow i).isLt at hentry
    unfold Matrix.mulVec Matrix.row Vector.dotProduct at hentry
    rw [Vector.getElem_ofFn (E.toIsEchelonForm.pivotRow i).isLt] at hentry
    rw [Vector.getElem_zero (E.toIsEchelonForm.pivotRow i).val
      (E.toIsEchelonForm.pivotRow i).isLt] at hentry
    exact hentry
  -- Split the foldl using the perm `finRange m ~ pivotCols.toList ++ freeColsList`.
  have hperm := finRange_perm_pivot_free (M := M) (D := D) E.toIsEchelonForm
  have hSplit :
      (List.finRange m).foldl
          (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 =
        D.pivotCols.toList.foldl
            (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 +
        E.toIsEchelonForm.freeColsList.foldl
            (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 := by
    rw [List.foldl_add_perm
      (f := fun l => D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) hperm]
    rw [List.foldl_append]
    rw [List.foldl_add_eq_add_foldl (R := R)
      (xs := E.toIsEchelonForm.freeColsList)
      (f := fun l => D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l])
      (z := D.pivotCols.toList.foldl
        (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0)]
  -- Pivot half: convert to fold over Fin D.rank, use indicator structure.
  have hPivotPart :
      D.pivotCols.toList.foldl
          (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 =
        v[D.pivotCols.get i] := by
    have hList : D.pivotCols.toList =
        (List.finRange D.rank).map fun i' => D.pivotCols.get i' := by
      have h := vector_toList_eq_finRange_map_get D.pivotCols
      simpa [Vector.get] using h
    rw [hList, List.foldl_map]
    have hrewrite :
        (List.finRange D.rank).foldl
            (fun acc i' =>
              acc + D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i'] *
                v[D.pivotCols.get i']) 0 =
          (List.finRange D.rank).foldl
            (fun acc i' =>
              acc + (if i = i' then (1 : R) else 0) * v[D.pivotCols.get i']) 0 := by
      apply List.foldl_add_congr
      intro i' _hi'
      have h := pivot_column_entry_pivotRow E i i'
      rw [h]
      by_cases hii : i' = i
      · subst i'
        rfl
      · have hii' : i ≠ i' := fun h => hii h.symm
        rw [if_neg hii, if_neg hii']
    rw [hrewrite]
    rw [foldl_indicator_mul_unique (List.finRange D.rank) i
      (fun i' => v[D.pivotCols.get i'])
      (List.mem_finRange i) (List.nodup_finRange D.rank) 0]
    grind
  -- Free half: convert to fold over Fin (m - D.rank).
  have hFreePart :
      E.toIsEchelonForm.freeColsList.foldl
          (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 =
        (List.finRange (m - D.rank)).foldl
          (fun acc k =>
            acc +
              D.echelon[E.toIsEchelonForm.pivotRow i][E.toIsEchelonForm.freeCols.get k] *
                v[E.toIsEchelonForm.freeCols.get k]) 0 := by
    have hList : E.toIsEchelonForm.freeColsList =
        (List.finRange (m - D.rank)).map fun k => E.toIsEchelonForm.freeCols.get k := by
      apply List.ext_getElem
      · simp [E.toIsEchelonForm.freeColsList_length]
      · intro k hk₁ _
        have hk : k < m - D.rank := by
          rw [E.toIsEchelonForm.freeColsList_length] at hk₁
          exact hk₁
        rw [List.getElem_map, List.getElem_finRange]
        change E.toIsEchelonForm.freeColsList[k]'_ = E.toIsEchelonForm.freeCols.get ⟨k, hk⟩
        unfold IsEchelonForm.freeCols
        simp [Vector.get, List.getElem_toArray]
    rw [hList, List.foldl_map]
  rw [hSplit, hPivotPart, hFreePart] at hZero
  exact hZero

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
/-- Every nullspace vector is generated by the computed nullspace basis. -/
theorem nullspace_complete {R : Type u} [Lean.Grind.Field R] {n m : Nat}
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsRowReduced M D) (v : Vector R m) :
    M * v = 0 → ∃ c : Vector R (m - D.rank), E.nullspaceMatrix * c = v := by
  intro hMv
  have hEchelon : D.echelon * v = 0 := by
    calc
      D.echelon * v = (D.transform * M) * v := by rw [E.toIsEchelonForm.transform_mul]
      _ = D.transform * (M * v) := Matrix.mul_assoc_vec _ _ _
      _ = D.transform * (0 : Vector R n) := by rw [hMv]
      _ = 0 := Matrix.mulVec_zero _
  refine ⟨Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]), ?_⟩
  -- Prove the entry-wise equality for an arbitrary `Fin m` index, then convert
  -- to the `Vector.ext` form. Working with `Fin` lets us use `subst` on the
  -- `colPartition` hypothesis without dependent-type rewriting issues.
  have hcEntry : ∀ k : Fin (m - D.rank),
      (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
          Vector R (m - D.rank))[k] =
        v[E.toIsEchelonForm.freeCols.get k] := by
    intro k
    simp [Vector.getElem_ofFn]
  have key : ∀ jj : Fin m,
      (E.nullspaceMatrix *
          (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
            Vector R (m - D.rank)))[jj.val]'jj.isLt = v[jj.val]'jj.isLt := by
    intro jj
    -- Expand the matrix-vector product to a foldl.
    change
      (Matrix.mulVec E.nullspaceMatrix
        (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
          Vector R (m - D.rank)))[jj.val]'jj.isLt = v[jj.val]'jj.isLt
    unfold Matrix.mulVec Matrix.row Vector.dotProduct
    rw [Vector.getElem_ofFn jj.isLt]
    change
      (List.finRange (m - D.rank)).foldl
          (fun acc k =>
            acc + E.nullspaceMatrix[jj][k] *
              (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
                Vector R (m - D.rank))[k]) 0 = v[jj]
    rcases E.toIsEchelonForm.colPartition jj with ⟨i, hi⟩ | ⟨l, hl⟩
    · -- Pivot case: substitute jj := D.pivotCols.get i
      subst hi
      -- Replace v[D.pivotCols.get i] using the freeSum identity.
      have hRowEq :
          (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc + E.nullspaceMatrix[D.pivotCols.get i][k] *
                  (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
                    Vector R (m - D.rank))[k]) 0 =
            (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc +
                  -(D.echelon[E.toIsEchelonForm.pivotRow i][
                      E.toIsEchelonForm.freeCols.get k] *
                    v[E.toIsEchelonForm.freeCols.get k])) 0 := by
        apply List.foldl_add_congr
        intro k _hk
        rw [nullspaceMatrix_pivot E i k, hcEntry k]
        grind
      rw [hRowEq]
      have hFree := freeSum_eq_neg_pivot E hEchelon i
      have hNeg :
          (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc +
                  -(D.echelon[E.toIsEchelonForm.pivotRow i][
                      E.toIsEchelonForm.freeCols.get k] *
                    v[E.toIsEchelonForm.freeCols.get k])) 0 =
            -((List.finRange (m - D.rank)).foldl
                (fun acc k =>
                  acc +
                    D.echelon[E.toIsEchelonForm.pivotRow i][
                      E.toIsEchelonForm.freeCols.get k] *
                      v[E.toIsEchelonForm.freeCols.get k]) 0) := by
        have hmul := (List.foldl_add_mul_left
          (xs := List.finRange (m - D.rank))
          (f := fun k =>
            D.echelon[E.toIsEchelonForm.pivotRow i][E.toIsEchelonForm.freeCols.get k] *
              v[E.toIsEchelonForm.freeCols.get k])
          (c := (-1 : R)) (z := 0)).symm
        have hzero : ((-1 : R)) * 0 = 0 := by grind
        rw [hzero] at hmul
        have h1 :
            (List.finRange (m - D.rank)).foldl
                (fun acc k =>
                  acc +
                    -(D.echelon[E.toIsEchelonForm.pivotRow i][
                        E.toIsEchelonForm.freeCols.get k] *
                      v[E.toIsEchelonForm.freeCols.get k])) 0 =
              (List.finRange (m - D.rank)).foldl
                (fun acc k =>
                  acc +
                    ((-1 : R) *
                      (D.echelon[E.toIsEchelonForm.pivotRow i][
                          E.toIsEchelonForm.freeCols.get k] *
                        v[E.toIsEchelonForm.freeCols.get k]))) 0 := by
          apply List.foldl_add_congr
          intro k _hk
          grind
        rw [h1, ← hmul]
        grind
      rw [hNeg]
      have hsum :
          (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc +
                  D.echelon[E.toIsEchelonForm.pivotRow i][
                    E.toIsEchelonForm.freeCols.get k] *
                    v[E.toIsEchelonForm.freeCols.get k]) 0 =
            -v[D.pivotCols.get i] := by
        have h := hFree
        grind
      rw [hsum]
      grind
    · -- Free case: substitute jj := freeCols.get l
      subst hl
      have hcongr :
          (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc + E.nullspaceMatrix[E.toIsEchelonForm.freeCols.get l][k] *
                  (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
                    Vector R (m - D.rank))[k]) 0 =
            (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc + (if l = k then (1 : R) else 0) *
                  v[E.toIsEchelonForm.freeCols.get k]) 0 := by
        apply List.foldl_add_congr
        intro k _hk
        rw [hcEntry k]
        by_cases hkl : k = l
        · subst k
          rw [nullspaceMatrix_free E l, if_pos rfl]
        · have hlk : l ≠ k := fun heq => hkl heq.symm
          rw [nullspaceMatrix_free_ne E (k := k) (l := l) hkl, if_neg hlk]
      rw [hcongr]
      rw [foldl_indicator_mul_unique (List.finRange (m - D.rank)) l
        (fun k => v[E.toIsEchelonForm.freeCols.get k])
        (List.mem_finRange l) (List.nodup_finRange (m - D.rank)) 0]
      grind
  ext j hj
  exact key ⟨j, hj⟩

end IsRowReduced

end Matrix
end Hex
