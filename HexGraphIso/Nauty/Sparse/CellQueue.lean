/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.QueueReplace

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every active queue entry is the beginning of a partition cell, and the
queue agrees exactly with the packed active set. -/
structure CellQueue (ptn : Array Nat) (level : Nat) (active : VSet n) (queue : Array Nat) : Prop where
  set : ActiveQueue active queue
  starts : ∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ level

namespace CellQueue

variable {n level v pos : Nat} {ptn after queue : Array Nat} {active : VSet n}

theorem of_scan (h : ActiveScan active queue none)
    (hs : ∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ level) :
    CellQueue ptn level active queue := ⟨ActiveQueue.of_scan h, hs⟩

/-- An open interior position cannot already be an active cell start. -/
theorem fresh (h : CellQueue ptn level active queue) (hv : 0 < v)
    (ho : level < ptn[v - 1]!) : active.mem v = false := by
  cases he : active.mem v with
  | false => rfl
  | true => have := h.starts v he; omega

theorem partition (h : CellQueue ptn level active queue)
    (hc : ∀ q : Nat, ptn[q]! ≤ level → after[q]! ≤ level) : CellQueue after level active queue := by
  refine ⟨h.set, ?_⟩
  intro v hv
  exact (h.starts v hv).imp_right (hc _)

theorem cut (h : CellQueue ptn level active queue) (q : Nat) :
    CellQueue (ptn.setIfInBounds q level) level active queue := by
  apply h.partition
  intro j hj
  by_cases he : q = j
  · subst j
    by_cases hb : q < ptn.size
    · rw [← Array.set!_eq_setIfInBounds, Array.getElem!_set!_self _ _ _ hb]
      exact Nat.le_refl _
    · simpa only [Array.setIfInBounds_eq_of_size_le (xs := ptn) (i := q) (by omega)] using hj
  · rw [← Array.set!_eq_setIfInBounds, Array.getElem!_set!_ne _ _ _ _ he]
    exact hj

theorem push (h : CellQueue ptn level active queue) (hv : v < n)
    (hs : v = 0 ∨ ptn[v - 1]! ≤ level) (hf : active.mem v = false) :
    CellQueue ptn level (active.insert v) (queue.push v) := by
  refine ⟨h.set.push hv hf, ?_⟩
  intro w hw
  rw [VSet.mem_insert_of_lt active hv] at hw
  simp only [Bool.or_eq_true] at hw
  rcases hw with hw | hw
  · exact h.starts w hw
  · have he : v = w := by simpa using hw
    simpa only [← he] using hs

/-- A new interior cut creates a fresh active cell start. -/
theorem cut_push (h : CellQueue ptn level active queue) (hv : 0 < v)
    (hn : v < n) (hb : v - 1 < ptn.size) (ho : level < ptn[v - 1]!) :
    CellQueue (ptn.setIfInBounds (v - 1) level) level (active.insert v) (queue.push v) := by
  apply (h.cut (v - 1)).push hn ?_ (h.fresh hv ho)
  right
  rw [← Array.set!_eq_setIfInBounds, Array.getElem!_set!_self _ _ _ hb]
  exact Nat.le_refl _

theorem cut_next (h : CellQueue ptn level active queue) (q : Nat)
    (hn : q + 1 < n) (hb : q < ptn.size) (ho : level < ptn[q]!) :
    CellQueue (ptn.setIfInBounds q level) level (active.insert (q + 1))
      (queue.push (q + 1)) := by
  simpa only [Nat.add_sub_cancel] using h.cut_push (v := q + 1) (by omega) hn
    (by simpa only [Nat.add_sub_cancel] using hb)
    (by simpa only [Nat.add_sub_cancel] using ho)

theorem remove (h : CellQueue ptn level active queue) (hp : pos < queue.size) :
    CellQueue ptn level (active.erase queue[pos]!)
      ((queue.setIfInBounds pos queue[queue.size - 1]!).pop) := by
  refine ⟨h.set.remove hp, ?_⟩
  intro w hw
  rw [VSet.mem_erase] at hw
  simp only [Bool.and_eq_true] at hw
  exact h.starts w hw.1

theorem replace (h : CellQueue ptn level active queue) (hp : pos < queue.size)
    (hv : v < n) (hs : v = 0 ∨ ptn[v - 1]! ≤ level) (hf : active.mem v = false) :
    CellQueue ptn level ((active.erase queue[pos]!).insert v) (queue.setIfInBounds pos v) := by
  refine ⟨h.set.replace hp hv hf, ?_⟩
  intro w hw
  rw [VSet.mem_insert_of_lt _ hv, VSet.mem_erase] at hw
  simp only [Bool.or_eq_true] at hw
  rcases hw with hw | hw
  · simp only [Bool.and_eq_true] at hw
    exact h.starts w hw.1
  · have he : v = w := by simpa using hw
    simpa only [← he] using hs

theorem replace_get (h : CellQueue ptn level active queue) (hp : pos < queue.size)
    (hv : v < n) (hs : v = 0 ∨ ptn[v - 1]! ≤ level) (hf : active.mem v = false) :
    CellQueue ptn level ((active.erase queue[pos]).insert v) (queue.setIfInBounds pos v) := by
  simpa only [getElem!_pos queue pos hp] using h.replace hp hv hs hf

end CellQueue

end Hex.GraphIso.Nauty.Sparse
