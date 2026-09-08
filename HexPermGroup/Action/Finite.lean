/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Action.Build
public import HexPermGroup.Enumerate

public section

namespace Hex.PermGroup.Action

variable {G : Group n} {α : Type u} {a : Action G α} {x : α}

theorem Queue.reps_nodup (t : Queue a x) : t.orbit.reps.toList.Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij he
  have hi' : i < t.objects.size := by simpa [Queue.orbit] using hi
  have hj' : j < t.objects.size := by simpa [Queue.orbit] using hj
  have him := congrArg (fun p : Element G => a.act p x) he
  simp only [Vector.getElem_toList, Queue.orbit, Hex.Vector.getElem_ofFn',
    t.image ⟨i, hi'⟩, t.image ⟨j, hj'⟩] at him
  have := t.nodup.getElem_inj.mp him
  omega

/-- Distinct discovered objects require distinct group elements. This counting
argument is erased; traversal never enumerates the group. -/
theorem Exhausted.tooSmall_order (e : Exhausted a x cap) : cap < G.order := by
  obtain ⟨y, ⟨p, hp⟩, hnew⟩ := e.more
  have hnot : p ∉ e.queue.orbit.reps.toList := by
    intro hm
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    have hi' : i < e.queue.objects.size := by simpa [Queue.orbit] using hi
    have hv : e.queue.arena.values[e.queue.roots[i]]'(e.queue.bound ⟨i, hi'⟩) = p := by
      simpa [Queue.orbit] using he
    have him := e.queue.image ⟨i, hi'⟩
    rw [hv, hp] at him
    exact hnew (him.symm ▸ Array.getElem_mem hi')
  have hn : (p :: e.queue.orbit.reps.toList).Nodup :=
    List.nodup_cons.mpr ⟨hnot, e.queue.reps_nodup⟩
  have hlen := List.nodup_subset_length_le hn (l₂ := G.enumerate.toList)
    (fun q _ => by simpa using G.mem_enumerate q)
  have hh : cap + 1 ≤ G.order := by simpa [Queue.orbit, e.full, Group.enumerate_size] using hlen
  omega

theorem OrbitLimit.tooSmall_order (e : OrbitLimit a x cap) : cap < G.order := by
  cases e with
  | zero he => rw [he]; exact G.order_pos
  | full e => exact e.tooSmall_order

/-- Every action orbit is finite. Existence is proved using the group-order
bound; clients retain their own explicit, usually much smaller object budgets. -/
theorem exists_orbit [DecidableEq α] (a : Action G α) (x : α) :
    ∃ c : Orbit G α, c.Valid a x := by
  cases he : a.breadthFirst x G.order with
  | ok c => exact ⟨c.val, c.property.1⟩
  | error e => have := e.tooSmall_order; omega

end Hex.PermGroup.Action
