/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Window

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A write at the end of a retained prefix appends exactly that vertex. -/
theorem take_set (lab : Array Nat) (k v : Nat) (hk : k < lab.size) :
    (lab.setIfInBounds k v).toList.take (k + 1) = lab.toList.take k ++ [v] := by
  simp only [Array.toList_setIfInBounds]
  rw [List.take_succ_eq_append_getElem (by simpa using hk), List.take_set,
    List.set_eq_of_length_le (by simp only [List.length_take]; exact Nat.min_le_left _ _), List.getElem_set_self]

/-- The singleton splitter compacts the vertices that do not meet the
splitter while collecting the others. Unread source positions are retained. -/
structure Compact (before : Array Nat) (p : Nat → Bool) (first upto : Nat)
    (seen : List Nat) (lab hit : Array Nat) (next : Nat) : Prop where
  bounds : first ≤ next ∧ next ≤ upto ∧ upto ≤ before.size
  size : lab.size = before.size
  count : next = first + (seen.filter fun v => !p v).length
  kept : lab.toList.take next = before.toList.take first ++ seen.filter (fun v => !p v)
  hits : hit.toList = seen.filter p
  exterior : ∀ q, q < before.size → (q < first ∨ upto ≤ q) → lab[q]! = before[q]!

namespace Compact

theorem initial (before : Array Nat) (p : Nat → Bool) (first : Nat)
    (hb : first ≤ before.size) : Compact before p first first [] before #[] first := by
  refine ⟨by omega, rfl, ?_, ?_, ?_, ?_⟩ <;> simp

theorem collect (h : Compact before p first upto seen lab hit next)
    (hb : upto < before.size) (hv : p before[upto]! = true) :
    Compact before p first (upto + 1) (seen ++ [before[upto]!]) lab
      (hit.push before[upto]!) next := by
  refine ⟨by have := h.bounds; omega, h.size, ?_, ?_, ?_, ?_⟩
  · simpa only [List.filter_append, List.filter_cons, List.filter_nil, hv,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_nil] using h.count
  · simpa only [List.filter_append, List.filter_cons, List.filter_nil, hv,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_nil] using h.kept
  · simp only [Array.toList_push, h.hits, List.filter_append, List.filter_cons, List.filter_nil,
      hv, ↓reduceIte]
  · intro q hq ho
    exact h.exterior q hq (by omega)

theorem keep (h : Compact before p first upto seen lab hit next)
    (hb : upto < before.size) (hv : p before[upto]! = false) :
    Compact before p first (upto + 1) (seen ++ [before[upto]!])
      (lab.setIfInBounds next before[upto]!) hit (next + 1) := by
  have bounds := h.bounds
  have hn : next < lab.size := by rw [h.size]; omega
  refine ⟨by omega, by simpa using h.size, ?_, ?_, ?_, ?_⟩
  · simp only [List.filter_append, List.filter_cons, List.filter_nil, hv,
      Bool.not_false, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
    rw [h.count]
    omega
  · rw [take_set lab next _ hn, h.kept]
    simp only [List.filter_append, List.filter_cons, List.filter_nil, hv,
      Bool.not_false, ↓reduceIte, List.append_assoc]
  · simpa only [List.filter_append, List.filter_cons, List.filter_nil, hv,
      Bool.false_eq_true, ↓reduceIte, List.append_nil] using h.hits
  · intro q hq ho
    rw [← Array.set!_eq_setIfInBounds, Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact h.exterior q hq (by omega)

end Compact

end Hex.GraphIso.Nauty.Sparse
