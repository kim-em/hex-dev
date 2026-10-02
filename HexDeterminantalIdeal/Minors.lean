/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminant
public import HexDeterminantalIdeal.Choose

public section

/-!
Executable minors and determinantal-ideal generators.

`minors r A` lists every `r × r` minor of `A`: the determinant of
`selectedSubmatrix A rows cols` for strictly increasing `rows` and `cols`,
enumerated through `selectedColumnTuples` (rows outer, columns inner, both in
colexicographic order). `detIdealGens r A` drops the zero minors and exact
duplicates and is a generating list for the `r`-th determinantal ideal
`I_r(A)`.

The conventions at the boundaries follow from the definitions: `minors 0 A =
[1]` (one empty minor, whose determinant is `1`) and `minors r A = []` once
`r` exceeds a dimension. The invariance expansions `minor_mul_left_expand` and
`minor_mul_right_expand` are Cauchy-Binet with the factors named: every minor
of `P * A` or `A * Q` is a combination of minors of `A`.
-/

namespace Hex
universe u v
namespace Matrix

variable {R : Type u} {n m : Nat}

/-- Every `r × r` minor of `A`, rows outer and columns inner, each in the
order of `selectedColumnTuples`. -/
@[expose]
def minors [Lean.Grind.Ring R] (r : Nat) (A : Matrix R n m) : List R :=
  (selectedColumnTuples r n).flatMap fun rows =>
    (selectedColumnTuples r m).map fun cols => det (selectedSubmatrix A rows cols)

/-- The nonzero, pairwise distinct `r × r` minors, keeping first occurrences:
a generating list for the determinantal ideal `I_r(A)`. -/
@[expose]
def detIdealGens [Lean.Grind.Ring R] [DecidableEq R] (r : Nat) (A : Matrix R n m) : List R :=
  ((minors r A).filter fun x => decide (x ≠ 0)).eraseDups

/-! # Enumeration -/

/-- Membership in `minors`: the minors indexed by strictly increasing tuples. -/
theorem mem_minors_iff [Lean.Grind.Ring R] (A : Matrix R n m) (r : Nat) (x : R) :
    x ∈ minors r A ↔ ∃ rows ∈ selectedColumnTuples r n, ∃ cols ∈ selectedColumnTuples r m,
      x = det (selectedSubmatrix A rows cols) := by
  unfold minors
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨rows, hrows, cols, hcols, rfl⟩
    exact ⟨rows, hrows, cols, hcols, rfl⟩
  · rintro ⟨rows, hrows, cols, hcols, rfl⟩
    exact ⟨rows, hrows, cols, hcols, rfl⟩

/-- `minors r A` has one member per row selection and column selection. -/
theorem length_minors [Lean.Grind.Ring R] (A : Matrix R n m) (r : Nat) :
    (minors r A).length = Nat.choose n r * Nat.choose m r := by
  unfold minors
  rw [← length_selectedColumnTuples r n, ← length_selectedColumnTuples r m]
  generalize selectedColumnTuples r n = xs
  generalize selectedColumnTuples r m = ys
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons,
      Nat.succ_mul, Nat.add_comm]

/-- The determinant of the `0 × 0` matrix is `1`. -/
theorem det_fin_zero [Lean.Grind.Ring R] (M : Matrix R 0 0) : det M = 1 := by
  simp [det, detTerm, detSign, detProduct, permutationVectors, inversionCount]
  grind

/-- There is one empty tuple. -/
theorem selectedColumnTuples_zero (n : Nat) : selectedColumnTuples 0 n = [#v[]] := rfl

/-- There is exactly one `0 × 0` minor, and it is `1`. -/
theorem minors_zero [Lean.Grind.Ring R] (A : Matrix R n m) : minors 0 A = [1] := by
  unfold minors
  rw [selectedColumnTuples_zero, selectedColumnTuples_zero]
  simp [det_fin_zero]

/-- The enumeration is empty exactly when `n < r`. -/
theorem selectedColumnTuples_eq_nil_iff (r n : Nat) :
    selectedColumnTuples r n = [] ↔ n < r := by
  constructor
  · intro h
    apply Nat.lt_of_not_le
    intro hle
    let cols : Vector (Fin n) r := Vector.ofFn fun i => ⟨i.val, by omega⟩
    have hsi : IsStrictlyIncreasingColumnTuple cols := by
      intro i j hij
      simp [cols, hij]
    have hmem := (mem_selectedColumnTuples_iff cols).mpr hsi
    rw [h] at hmem
    exact List.not_mem_nil hmem
  · exact selectedColumnTuples_eq_nil_of_lt

/-- `minors r A` is empty exactly when `r` exceeds a dimension. -/
theorem minors_eq_nil_iff [Lean.Grind.Ring R] (A : Matrix R n m) (r : Nat) :
    minors r A = [] ↔ n < r ∨ m < r := by
  unfold minors
  rw [List.flatMap_eq_nil_iff]
  constructor
  · intro h
    by_cases hn : n < r
    · exact Or.inl hn
    · right
      rcases hlist : selectedColumnTuples r n with _ | ⟨rows, rest⟩
      · exact absurd ((selectedColumnTuples_eq_nil_iff r n).mp hlist) hn
      · have hrows : rows ∈ selectedColumnTuples r n := by
          rw [hlist]; exact List.mem_cons_self
        have hnil := h rows hrows
        rw [List.map_eq_nil_iff] at hnil
        exact (selectedColumnTuples_eq_nil_iff r m).mp hnil
  · intro h rows hrows
    rcases h with h | h
    · rw [selectedColumnTuples_eq_nil_of_lt h] at hrows
      exact absurd hrows List.not_mem_nil
    · rw [selectedColumnTuples_eq_nil_of_lt h]
      rfl

open _root_.List in
/-- Distributing a `cons` through a `flatMap` splits off the heads. -/
private theorem flatMap_cons_perm {β : Type v} {γ : Type _}
    (zs : List β) (f : β → γ) (g : β → List γ) :
    (zs.flatMap fun y => f y :: g y).Perm (zs.map f ++ zs.flatMap g) := by
  induction zs with
  | nil => simp
  | cons y zs ihy =>
    simp only [List.flatMap_cons, List.map_cons, List.cons_append]
    apply List.Perm.cons
    calc g y ++ zs.flatMap (fun y => f y :: g y)
        _ ~ g y ++ (zs.map f ++ zs.flatMap g) := ihy.append_left _
        _ = (g y ++ zs.map f) ++ zs.flatMap g := by rw [List.append_assoc]
        _ ~ (zs.map f ++ g y) ++ zs.flatMap g := List.perm_append_comm.append_right _
        _ = zs.map f ++ (g y ++ zs.flatMap g) := by rw [List.append_assoc]

open _root_.List in
/-- Swapping the two nested enumerations of a doubly indexed list permutes it. -/
private theorem flatMap_map_swap_perm {α : Type u} {β : Type v} {γ : Type _}
    (xs : List α) (ys : List β) (g : α → β → γ) :
    (xs.flatMap fun x => ys.map fun y => g x y).Perm
      (ys.flatMap fun y => xs.map fun x => g x y) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_cons]
    exact (ih.append_left _).trans
      (flatMap_cons_perm ys (fun y => g x y) (fun y => xs.map fun x => g x y)).symm

/-- The minors of the transpose are the minors of the matrix, in the order
with the roles of the two enumerations swapped. -/
theorem minors_transpose [Lean.Grind.CommRing R] (A : Matrix R n m) (r : Nat) :
    (minors r A.transpose).Perm (minors r A) := by
  unfold minors
  refine (flatMap_map_swap_perm (selectedColumnTuples r m) (selectedColumnTuples r n)
    fun rows cols => det (selectedSubmatrix A.transpose rows cols)).trans ?_
  have heq : ((selectedColumnTuples r n).flatMap fun cols =>
        (selectedColumnTuples r m).map fun rows => det (selectedSubmatrix A.transpose rows cols)) =
      (selectedColumnTuples r n).flatMap fun rows =>
        (selectedColumnTuples r m).map fun cols => det (selectedSubmatrix A rows cols) := by
    congr 1
    funext cols
    congr 1
    funext rows
    rw [selectedSubmatrix_transpose, det_transpose]
  rw [heq]

/-- Membership in the generating list: the nonzero minors. -/
theorem mem_detIdealGens_iff [Lean.Grind.Ring R] [DecidableEq R] (A : Matrix R n m) (r : Nat)
    (x : R) :
    x ∈ detIdealGens r A ↔ x ∈ minors r A ∧ x ≠ 0 := by
  unfold detIdealGens
  rw [List.mem_eraseDups, List.mem_filter, decide_eq_true_iff]

/-! # Deleting a row and a column of a selected submatrix -/

/-- Erasing position `i` of a tuple reads the remaining entries through
`skipIndex i`. -/
theorem getElem_eraseIdx_skipIndex {α : Type v} {k : Nat} (v : Vector α (k + 1))
    (i : Fin (k + 1)) (a : Fin k) :
    (v.eraseIdx i)[a] = v[skipIndex i a] := by
  simp only [Fin.getElem_fin]
  rw [Vector.getElem_eraseIdx]
  by_cases h : a.val < i.val
  · rw [dite_eq_left h]
    simp [skipIndex, h]
  · rw [dite_eq_right h]
    simp [skipIndex, h]

/-- Deleting a row and a column of a selected submatrix selects the tuples with
those positions erased. -/
theorem deleteRowCol_selectedSubmatrix {k : Nat} (A : Matrix R n m)
    (rows : Vector (Fin n) (k + 1)) (cols : Vector (Fin m) (k + 1)) (i j : Fin (k + 1)) :
    deleteRowCol (selectedSubmatrix A rows cols) i j =
      selectedSubmatrix A (rows.eraseIdx i) (cols.eraseIdx j) := by
  apply ext_getElem
  intro a b
  rw [getElem_deleteRowCol, getElem_selectedSubmatrix, getElem_selectedSubmatrix]
  simp only [getElem_eraseIdx_skipIndex]

/-- Erasing a position of a strictly increasing tuple leaves it strictly
increasing. -/
theorem isStrictlyIncreasingColumnTuple_eraseIdx {k : Nat} {cols : Vector (Fin m) (k + 1)}
    (h : IsStrictlyIncreasingColumnTuple cols) (i : Fin (k + 1)) :
    IsStrictlyIncreasingColumnTuple (cols.eraseIdx i) := by
  intro a b hab
  rw [getElem_eraseIdx_skipIndex, getElem_eraseIdx_skipIndex]
  apply h
  unfold skipIndex
  split <;> split <;> simp <;> omega

/-! # Invariance under multiplication -/

/-- Every `r × r` minor of `P * A` is a combination of `r × r` minors of `A`,
with coefficients the minors of `P`: Cauchy-Binet with the factors named. -/
theorem minor_mul_left_expand [Lean.Grind.CommRing R] {q r : Nat}
    (P : Matrix R q n) (A : Matrix R n m)
    (rows : Vector (Fin q) r) (cols : Vector (Fin m) r) :
    det (selectedSubmatrix (P * A) rows cols) =
      (selectedColumnTuples r n).foldl (fun acc middle => acc +
        det (selectedSubmatrix A middle cols) * det (selectedSubmatrix P rows middle)) 0 :=
  det_minor_mul P A rows cols

/-- Every `r × r` minor of `A * Q` is a combination of `r × r` minors of `A`,
with coefficients the minors of `Q`. -/
theorem minor_mul_right_expand [Lean.Grind.CommRing R] {q r : Nat}
    (A : Matrix R n m) (Q : Matrix R m q)
    (rows : Vector (Fin n) r) (cols : Vector (Fin q) r) :
    det (selectedSubmatrix (A * Q) rows cols) =
      (selectedColumnTuples r m).foldl (fun acc middle => acc +
        det (selectedSubmatrix Q middle cols) * det (selectedSubmatrix A rows middle)) 0 :=
  det_minor_mul A Q rows cols

end Matrix
end Hex
