/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraph.Sparse.Build

@[expose] public section

namespace Hex.SparseGraph.Builder

/-- Map and normalize a compressed row. -/
def mapRow (xs : Array (Fin n)) (f : Fin n → Fin n) : List (Fin n) :=
  normalize (xs.toList.map f)

private theorem get_marks (xs : List (Fin n)) (f : Fin n → Fin n)
    (marks : Vector Bool n) (i : Fin n) :
    (xs.foldl (fun a v => a.set (f v).val true) marks)[i.val] =
      (marks[i.val] || decide (i ∈ xs.map f)) := by
  induction xs generalizing marks with
  | nil => simp
  | cons v xs ih =>
    rw [List.foldl_cons, ih]
    by_cases h : f v = i <;>
      simp [Vector.getElem_set, List.map_cons, List.mem_cons, h, Fin.val_inj,
        eq_comm, Bool.or_assoc, Bool.or_left_comm]

/-- Emit a row in vertex order using a temporary membership array. -/
@[specialize] def countRow (xs : Array (Fin n)) (f : Fin n → Fin n) : List (Fin n) :=
  let marks := xs.foldl (fun (a : Vector Bool n) v => a.set (f v).val true)
    (Vector.replicate n false)
  (List.finRange n).filter fun i => marks[i.val]

private theorem mem_countRow (xs : Array (Fin n)) (f : Fin n → Fin n) (i : Fin n) :
    i ∈ countRow xs f ↔ i ∈ xs.toList.map f := by
  simp [countRow, ← Array.foldl_toList, get_marks]

private theorem sorted_countRow (xs : Array (Fin n)) (f : Fin n → Fin n) :
    (countRow xs f).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange n).filter _

theorem countRow_eq (xs : Array (Fin n)) (f : Fin n → Fin n) :
    countRow xs f = mapRow xs f := by
  have hs := sorted_countRow xs f
  have ht := sorted_normalize (xs.toList.map f)
  apply List.Perm.eq_of_pairwise (le := (· < ·))
    (fun a b _ _ hab hba => False.elim (Nat.lt_irrefl a.val (Nat.lt_trans hab hba))) hs ht
  apply (List.perm_ext_iff_of_nodup
    (hs.imp fun h => Fin.ne_of_lt h) (ht.imp fun h => Fin.ne_of_lt h)).mpr
  intro i
  simp [mem_countRow]

/-- Use counting only when its vertex scan is bounded by eight times the
row length. Sparse rows keep the existing merge sort. -/
@[inline] def mapRowFast (xs : Array (Fin n)) (f : Fin n → Fin n) : List (Fin n) :=
  if n ≤ 8 * xs.size then countRow xs f
  else normalize (xs.toList.map f)

@[csimp] theorem mapRow_eq_fast : @mapRow = @mapRowFast := by
  funext n xs f
  unfold mapRowFast
  split
  · exact (countRow_eq xs f).symm
  · rfl

end Hex.SparseGraph.Builder
