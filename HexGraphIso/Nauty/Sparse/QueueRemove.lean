/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ActiveQueue

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Replacing the final slot is popping and then pushing the new value. -/
theorem pop_push_set (a : Array Nat) (v : Nat) (ha : 0 < a.size) :
    a.pop.push v = a.setIfInBounds (a.size - 1) v := by
  apply Array.ext
  · simp only [Array.size_push, Array.size_pop, Array.size_setIfInBounds]
    omega
  · intro i hi hj
    simp only [Array.size_push, Array.size_pop] at hi
    by_cases he : i < a.size - 1
    · simp only [Array.getElem_push, Array.size_pop, he, ↓reduceDIte,
        Array.getElem_pop]
      exact (Array.getElem_setIfInBounds_ne (by omega) (by omega)).symm
    · have he' : i = a.size - 1 := by omega
      subst i
      simp only [Array.getElem_push, Array.size_pop, Nat.lt_irrefl, ↓reduceDIte,
        Array.getElem_setIfInBounds_self]

/-- The executed replacement-by-last-and-pop operation removes precisely
the selected occurrence, even when it is already the last entry. -/
theorem remove_perm (queue : Array Nat) (pos : Nat) (hp : pos < queue.size) :
    ((queue.setIfInBounds pos queue[queue.size - 1]!).pop).toList.Perm
      (queue.toList.erase queue[pos]!) := by
  have hs : 0 < queue.size := by omega
  have hx := exchange_perm queue pos (queue.size - 1) hp (by omega)
  simp only [Array.set!_eq_setIfInBounds] at hx
  have he := pop_push_set (queue.setIfInBounds pos queue[queue.size - 1]!) queue[pos]!
    (by simpa using hs)
  simp only [Array.size_setIfInBounds] at he
  rw [← he, Array.toList_push] at hx
  have hc : (queue[pos]! :: ((queue.setIfInBounds pos queue[queue.size - 1]!).pop).toList).Perm
      queue.toList :=
    (List.perm_append_comm (l₁ := [queue[pos]!]) (l₂ := _)).trans hx
  exact (List.cons_perm_iff_perm_erase.mp hc).2

/-- Removing the selected splitter retains exact agreement with the active
bitset, including last-position removal. -/
theorem ActiveQueue.remove (h : ActiveQueue active queue) (hp : pos < queue.size) :
    ActiveQueue (active.erase queue[pos]!)
      ((queue.setIfInBounds pos queue[queue.size - 1]!).pop) :=
  h.erase (remove_perm queue pos hp)

end Hex.GraphIso.Nauty.Sparse
