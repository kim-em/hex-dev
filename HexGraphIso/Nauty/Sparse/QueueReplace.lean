/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.QueueRemove

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Replacing a queue slot changes precisely its selected occurrence. -/
theorem replace_perm (queue : Array Nat) (pos v : Nat) (hp : pos < queue.size) :
    (queue.setIfInBounds pos v).toList.Perm (queue.toList.erase queue[pos]! ++ [v]) := by
  have hh := remove_perm (queue.push v) pos (by simpa using Nat.lt_succ_of_lt hp)
  have hlast : (queue.push v)[queue.size]! = v := by
    rw [getElem!_pos (queue.push v) queue.size (by simp)]
    simp
  have hpos : (queue.push v)[pos]! = queue[pos]! := by
    rw [getElem!_pos (queue.push v) pos (by simp; omega), getElem!_pos queue pos hp]
    simp only [Array.getElem_push, hp, ↓reduceDIte]
  have hpop : ((queue.push v).setIfInBounds pos v).pop = queue.setIfInBounds pos v := by
    simp only [Array.setIfInBounds_def, Array.size_push,
      show pos < queue.size + 1 by omega, ↓reduceDIte, Array.set_push, hp, Array.pop_push]
  have hm : queue[pos]! ∈ queue.toList := by
    rw [getElem!_pos queue pos hp, ← Array.getElem_toList hp]
    exact List.getElem_mem _
  simpa only [Array.size_push, Nat.add_sub_cancel, hlast, hpos, hpop, Array.toList_push,
    List.erase_append_left _ hm] using hh

namespace ActiveQueue

variable {n pos v : Nat} {active : VSet n} {queue out : Array Nat}

theorem permuted (h : ActiveQueue active queue) (hp : out.toList.Perm queue.toList) :
    ActiveQueue active out :=
  ⟨hp.nodup_iff.mpr h.nodup, fun v => hp.mem_iff.trans (h.mem v)⟩

/-- The largest-fragment replacement preserves the exact active set when
the replacement first cell was inactive. -/
theorem replace (h : ActiveQueue active queue) (hp : pos < queue.size)
    (hv : v < n) (hf : active.mem v = false) :
    ActiveQueue ((active.erase queue[pos]!).insert v) (queue.setIfInBounds pos v) := by
  have he : ActiveQueue (active.erase queue[pos]!) (queue.toList.erase queue[pos]!).toArray :=
    h.erase (by simp)
  have hf' : (active.erase queue[pos]!).mem v = false := by rw [VSet.mem_erase, hf]; rfl
  have hh := he.push hv hf'
  apply hh.permuted
  simpa only [Array.toList_push, List.toList_toArray] using replace_perm queue pos v hp

end ActiveQueue

end Hex.GraphIso.Nauty.Sparse
