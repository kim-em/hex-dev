/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraph.Sparse

@[expose] public section

namespace Hex.SparseGraph

@[inline] def packStep (acc : Array Nat × Array α) (row : List α) : Array Nat × Array α :=
  let (offsets, neighbors) := acc
  (offsets.push neighbors.size, neighbors ++ row)

/-- Append each row directly to its final array, recording offsets in the
same pass. No flattened intermediate list or row-length scan is needed. -/
def pack (rows : List (List α)) : Array Nat × Array α :=
  let (offsets, neighbors) := rows.foldl packStep (#[], #[])
  (offsets.push neighbors.size, neighbors)

private theorem pack_fold (rows : List (List α)) (offsets : Array Nat) (neighbors : Array α) :
    let result := rows.foldl packStep (offsets, neighbors)
    result.1.toList ++ [result.2.size] =
        offsets.toList ++ rows.scanl (fun off row => off + row.length) neighbors.size ∧
      result.2.toList = neighbors.toList ++ rows.flatten := by
  induction rows generalizing offsets neighbors with
  | nil => simp
  | cons row rows ih =>
    simp only [List.foldl_cons, packStep]
    have h := ih (offsets.push neighbors.size) (neighbors ++ row)
    have hsize : (neighbors ++ row).size = neighbors.size + row.length := by
      rw [← Array.length_toList, Array.toList_appendList]
      simp
    simpa [List.scanl_cons, Array.toList_push, Array.toList_appendList,
      List.flatten_cons, List.append_assoc, hsize] using h

theorem pack_eq (rows : List (List α)) :
    pack rows = ((offsetsOf rows).toArray, rows.flatten.toArray) := by
  have h := pack_fold rows #[] #[]
  apply Prod.ext
  · apply Array.toList_inj.mp
    simpa [pack, offsetsOf, Array.toList_push] using h.1
  · apply Array.toList_inj.mp
    simpa [pack] using h.2

/-- The checked graph constructor with direct array packing. -/
def ofRowsFast (rows : Vector (List (Fin n)) n)
    (hs : ∀ i : Fin n, (rows[i]).Pairwise (· < ·))
    (hr : ∀ i j : Fin n, j ∈ rows[i] ↔ i ∈ rows[j])
    (hl : ∀ i : Fin n, i ∉ rows[i]) : SparseGraph n :=
  let data := pack rows.toList
  have ho : data.1 = (offsetsOf rows.toList).toArray := congrArg Prod.fst (pack_eq rows.toList)
  have hn : data.2 = rows.toList.flatten.toArray := congrArg Prod.snd (pack_eq rows.toList)
  { offsets := data.1
    neighbors := data.2
    layout := by rw [ho, hn]; exact (ofRows rows hs hr hl).layout
    sorted i := by rw [ho, hn]; exact (ofRows rows hs hr hl).sorted i
    symm i j := by rw [ho, hn]; exact (ofRows rows hs hr hl).symm i j
    loopless i := by rw [ho, hn]; exact (ofRows rows hs hr hl).loopless i }

@[csimp] theorem ofRows_eq_fast : @ofRows = @ofRowsFast := by
  funext n rows hs hr hl
  apply ext_arrays <;> simp [ofRows, ofRowsFast, pack_eq]

end Hex.SparseGraph
