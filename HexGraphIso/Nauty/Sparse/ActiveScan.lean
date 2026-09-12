/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine
public import HexGraphIso.Nauty.Search.VSet.Card

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The initial active scan enumerates distinct members in ascending order;
`next` is the least member not yet in the queue. -/
structure ActiveScan (active : VSet n) (queue : Array Nat) (next : Option Nat) : Prop where
  ordered : queue.toList.Pairwise (· < ·)
  member : ∀ v ∈ queue.toList, active.mem v = true
  next_mem : ∀ v, next = some v → active.mem v = true
  ahead : ∀ v, next = some v → ∀ u ∈ queue.toList, u < v
  progress : ∀ v, next = some v → queue.size ≤ v
  covers : ∀ v, active.mem v = true →
    v ∈ queue.toList ∨ ∃ w, next = some w ∧ w ≤ v

namespace ActiveScan

theorem initial (active : VSet n) : ActiveScan active #[] (active.nextElem none) := by
  refine ⟨by simp, by simp, fun _ h => VSet.nextElem_mem h, by simp,
    by simp, ?_⟩
  intro v hv
  right
  cases hn : active.nextElem none with
  | none =>
    have := VSet.nextElem_none hn v (by simp [VSet.scanStart])
    simp [hv] at this
  | some w =>
    refine ⟨w, rfl, ?_⟩
    have hh := (VSet.nextElem_eq_some_iff.mp hn).2.2 v
    by_cases h : w ≤ v
    · exact h
    · have := hh (by simp [VSet.scanStart]) (by omega)
      simp [hv] at this

theorem step {active : VSet n} {queue : Array Nat} {next : Option Nat}
    (h : ActiveScan active queue next) (hn : next = some i) :
    ActiveScan active (queue.push i) (active.nextElem (some i)) := by
  have hi := h.next_mem i hn
  have ha := h.ahead i hn
  have hp := h.progress i hn
  have later : ∀ v, active.nextElem (some i) = some v → i < v := by
    intro v hv
    have := (VSet.nextElem_eq_some_iff.mp hv).2.1
    simp only [VSet.scanStart] at this
    omega
  refine ⟨?_, ?_, fun _ hv => VSet.nextElem_mem hv, ?_, ?_, ?_⟩
  · simpa only [Array.toList_push, List.pairwise_append, List.pairwise_singleton,
      List.mem_singleton, forall_eq, and_true, true_and] using And.intro h.ordered ha
  · intro v hv
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact h.member v hv
    · exact hi
  · intro v hv u hu
    have hl := later v hv
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · have := ha u hu; omega
    · exact hl
  · intro v hv
    have := later v hv
    simp only [Array.size_push]
    omega
  · intro v hv
    obtain hvq | ⟨w, hw, hle⟩ := h.covers v hv
    · left; simp [hvq]
    · have hw' : w = i := by simpa [hn] using hw.symm
      subst w
      by_cases he : v = i
      · subst v; left; simp
      · right
        cases hh : active.nextElem (some i) with
        | none =>
          have := VSet.nextElem_none hh v (by simp only [VSet.scanStart]; omega)
          simp [hv] at this
        | some u =>
          refine ⟨u, rfl, ?_⟩
          have hh := (VSet.nextElem_eq_some_iff.mp hh).2.2 v
          by_cases hu : u ≤ v
          · exact hu
          · have := hh (by simp only [VSet.scanStart]; omega) (by omega)
            simp [hv] at this

theorem size_le {active : VSet n} {queue : Array Nat} {next : Option Nat}
    (h : ActiveScan active queue next) : queue.size ≤ active.card := by
  have hd : queue.toList.Nodup := h.ordered.imp (fun hab => Nat.ne_of_lt hab)
  have hs : queue.toList ⊆ (List.range n).filter active.mem := by
    intro v hv
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (VSet.mem_lt (h.member v hv)), h.member v hv⟩
  have hh := hd.length_le_of_subset hs
  rw [VSet.card_eq_countBelow, VSet.countBelow, List.countP_eq_length_filter]
  exact hh

/-- Consuming `n` distinct bounded entries leaves no next member. -/
theorem exhausted {active : VSet n} {queue : Array Nat} {next : Option Nat}
    (h : ActiveScan active queue next) (hs : n ≤ queue.size) : next = none := by
  cases hn : next with
  | none => rfl
  | some v =>
    have := h.progress v hn
    have := VSet.mem_lt (h.next_mem v hn)
    omega

theorem complete {active : VSet n} {queue : Array Nat} {next : Option Nat}
    (h : ActiveScan active queue next) (hn : next = none) :
    ∀ v, v ∈ queue.toList ↔ active.mem v = true := by
  intro v
  refine ⟨h.member v, fun hv => ?_⟩
  obtain hv | ⟨w, hw, _⟩ := h.covers v hv
  · exact hv
  · simp [hn] at hw

end ActiveScan

end Hex.GraphIso.Nauty.Sparse
