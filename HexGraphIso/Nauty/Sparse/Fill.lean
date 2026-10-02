/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Compact

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Pointwise agreement above a position identifies the complete suffix. -/
theorem drop_eq {before after : Array Nat} {k : Nat}
    (hs : after.size = before.size)
    (he : ∀ q, q < before.size → k ≤ q → after[q]! = before[q]!) :
    after.toList.drop k = before.toList.drop k := by
  apply List.ext_getElem
  · simp [hs]
  · intro i hi hj
    have hb : k + i < before.size := by simp only [List.length_drop, Array.length_toList] at hj; omega
    have hh := he (k + i) hb (by omega)
    simpa only [List.getElem_drop, Array.getElem_toList,
      getElem!_pos after (k + i) (by omega), getElem!_pos before (k + i) hb] using hh

/-- Consecutive writes copy the prescribed list into an array while retaining
its prefix and unread suffix. -/
structure Fill (before : Array Nat) (data : List Nat) (first upto : Nat) (after : Array Nat) : Prop where
  fits : first + data.length ≤ before.size
  bound : upto ≤ data.length
  size : after.size = before.size
  copied : after.toList.take (first + upto) = before.toList.take first ++ data.take upto
  exterior : ∀ q, q < first ∨ first + upto ≤ q → after[q]! = before[q]!

namespace Fill

theorem initial (before : Array Nat) (data : List Nat) (first : Nat)
    (hb : first + data.length ≤ before.size) : Fill before data first 0 before := by
  refine ⟨hb, by omega, rfl, ?_, fun _ _ => rfl⟩
  simp

theorem step (h : Fill before data first upto after) (hb : upto < data.length) :
    Fill before data first (upto + 1) (after.setIfInBounds (first + upto) data[upto]!) := by
  have fits := h.fits
  have hi : first + upto < after.size := by rw [h.size]; omega
  refine ⟨fits, by omega, by simpa using h.size, ?_, ?_⟩
  · rw [← Nat.add_assoc, take_set after (first + upto) _ hi, h.copied,
      List.take_succ_eq_append_getElem hb]
    simp only [List.append_assoc, getElem!_pos data upto hb]
  · intro q hq
    rw [← Array.set!_eq_setIfInBounds, Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact h.exterior q (by omega)

/-- At completion all requested entries have been copied, with exact exterior
contents. This applies to the singleton splitter's reverse hit reinsertion. -/
theorem finish (h : Fill before data first data.length after) :
    after.toList = before.toList.take first ++ data ++ before.toList.drop (first + data.length) := by
  have ht := drop_eq h.size (fun q _ hq => h.exterior q (Or.inr hq))
  rw [← List.take_append_drop (first + data.length) after.toList, h.copied, ht]
  simp

end Fill

end Hex.GraphIso.Nauty.Sparse
