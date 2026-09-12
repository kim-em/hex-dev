/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ActiveScan
public import HexGraphIso.Nauty.Sparse.Rotate

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The mutable refinement queue enumerates the packed active set exactly
once; its order is the order used by nauty's splitter selection. -/
structure ActiveQueue (active : VSet n) (queue : Array Nat) : Prop where
  nodup : queue.toList.Nodup
  mem : ∀ v, v ∈ queue.toList ↔ active.mem v = true

namespace ActiveQueue

variable {n v : Nat} {active : VSet n} {queue out : Array Nat}

theorem of_scan (h : ActiveScan active queue none) : ActiveQueue active queue :=
  ⟨h.ordered.imp (fun hh => Nat.ne_of_lt hh), h.complete rfl⟩

theorem bound (h : ActiveQueue active queue) (hv : v ∈ queue.toList) : v < n :=
  VSet.mem_lt ((h.mem v).mp hv)

theorem push (h : ActiveQueue active queue) (hv : v < n) (hf : active.mem v = false) :
    ActiveQueue (active.insert v) (queue.push v) := by
  have hn : v ∉ queue.toList := by rw [h.mem, hf]; simp
  refine ⟨?_, ?_⟩
  · simp only [Array.toList_push, List.nodup_append, h.nodup, true_and]
    refine ⟨by simp, ?_⟩
    intro a ha b hb he
    have hb : b = v := by simpa using hb
    exact hn ((he.trans hb) ▸ ha)
  · intro w
    simp only [Array.toList_push, List.mem_append, List.mem_singleton,
      VSet.mem_insert_of_lt active hv, Bool.or_eq_true, beq_iff_eq, h.mem]
    exact or_congr Iff.rfl eq_comm

/-- Erasing a queue occurrence agrees with packed-set erasure because the
queue contains no duplicates. The array removal may reorder other entries. -/
theorem erase (h : ActiveQueue active queue)
    (hp : out.toList.Perm (queue.toList.erase v)) : ActiveQueue (active.erase v) out := by
  refine ⟨hp.nodup_iff.mpr (h.nodup.erase v), ?_⟩
  intro w
  rw [hp.mem_iff, h.nodup.mem_erase_iff, h.mem, VSet.mem_erase]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
  exact and_comm.trans (and_congr Iff.rfl ne_comm)

end ActiveQueue

end Hex.GraphIso.Nauty.Sparse
