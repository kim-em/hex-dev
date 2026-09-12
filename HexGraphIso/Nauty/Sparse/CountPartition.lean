/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MinimaBound
public import HexGraphIso.Nauty.Sparse.MinimaSort

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The processed boundary positions split exactly at a change of count.
Positions outside that prefix retain their original partition values. -/
structure CountPartition (level first upto : Nat) (lab hits before ptn : Array Nat) : Prop where
  size : ptn.size = before.size
  head : ∀ q : Nat, q < first → ptn[q]! = before[q]!
  cuts : ∀ q : Nat, first ≤ q → q < upto →
    ptn[q]! = if hits[lab[q]!]! = hits[lab[q + 1]!]! then before[q]! else level
  tail : ∀ q : Nat, upto ≤ q → ptn[q]! = before[q]!

namespace CountPartition

theorem constant (h : ∀ q, first ≤ q → q ≤ upto → hits[lab[q]!]! = value) :
    CountPartition level first upto lab hits ptn ptn := by
  refine ⟨rfl, fun _ _ => rfl, ?_, fun _ _ => rfl⟩
  intro q hq hu
  rw [h q hq (by omega), h (q + 1) (by omega) (by omega), ite_eq_left rfl]

theorem equal (h : CountPartition level first upto lab hits before ptn)
    (he : hits[lab[upto]!]! = hits[lab[upto + 1]!]!) :
    CountPartition level first (upto + 1) lab hits before ptn := by
  refine ⟨h.size, h.head, ?_, fun q hq => h.tail q (by omega)⟩
  intro q hq hu
  by_cases hqu : q < upto
  · exact h.cuts q hq hqu
  · have heq : q = upto := by omega
    subst q
    rw [ite_eq_left he]
    exact h.tail upto (Nat.le_refl _)

theorem different (h : CountPartition level first upto lab hits before ptn)
    (hl : first ≤ upto) (hb : upto < before.size)
    (he : hits[lab[upto]!]! ≠ hits[lab[upto + 1]!]!) :
    CountPartition level first (upto + 1) lab hits before (ptn.setIfInBounds upto level) := by
  change CountPartition level first (upto + 1) lab hits before (ptn.set! upto level)
  refine ⟨by simpa using h.size, ?_, ?_, ?_⟩
  · intro q hq
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact h.head q hq
  · intro q hq hu
    by_cases hqu : q < upto
    · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      exact h.cuts q hq hqu
    · have heq : q = upto := by omega
      subst q
      rw [Array.getElem!_set!_self _ _ _ (by rw [h.size]; exact hb), ite_eq_right he]
  · intro q hq
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact h.tail q (by omega)

/-- The first two nonempty minimum fragments need exactly one new boundary. -/
theorem minima (h : Minima lab hits first v2 v3 last w1 w2)
    (hv : v2 < v3) (hb : v2 - 1 < ptn.size) :
    CountPartition level first (v3 - 1) lab hits ptn (ptn.setIfInBounds (v2 - 1) level) := by
  have bounds := h.bounds
  change CountPartition level first (v3 - 1) lab hits ptn (ptn.set! (v2 - 1) level)
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro q hq
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
  · intro q hq hu
    by_cases he : q = v2 - 1
    · subst q
      rw [Array.getElem!_set!_self _ _ _ hb, h.minimum _ (by omega) (by omega),
        h.second _ (by omega) (by omega), ite_eq_right (by have := h.keys; omega)]
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm he)]
      by_cases hqv : q < v2
      · rw [h.minimum _ hq hqv, h.minimum _ (by omega) (by omega), ite_eq_left rfl]
      · rw [h.second _ (by omega) (by omega), h.second _ (by omega) (by omega), ite_eq_left rfl]
  · intro q hq
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]

end CountPartition

namespace Minima

/-- Sorting the larger-count tail retains both minimum fragments and their
strict separation from the tail. -/
theorem indirect (h : Minima lab hits first v2 v3 last w1 w2) (hb : last ≤ lab.size) :
    Minima (Sort.indirect lab hits v3 (last - v3)) hits first v2 v3 last w1 w2 := by
  have bounds := h.bounds
  have outside (q : Nat) (hq : q < v3) :
      (Sort.indirect lab hits v3 (last - v3))[q]! = lab[q]! :=
    Sort.indirect_outside lab hits v3 (last - v3) q (by omega) (Or.inl hq)
  refine ⟨bounds, h.keys, ?_, ?_, ?_⟩
  · intro q hq hu
    rw [outside q (by omega)]
    exact h.minimum q hq hu
  · intro q hq hu
    rw [outside q hu]
    exact h.second q hq hu
  · intro q hq hu
    have size := Sort.indirect_size lab hits v3 (last - v3)
    have perm := Sort.indirect_segment lab hits v3 (last - v3) (by omega)
    rw [show v3 + (last - v3) = last by omega] at perm
    obtain ⟨r, hrl, hru, hr⟩ := Sort.segment_mem (by omega) perm ⟨hq, hu⟩
    rw [hr]
    exact h.larger r hrl hru

theorem next_different (h : Minima lab hits first v2 v3 last w1 w2)
    (hv : v2 < v3) (ht : v3 < last) :
    hits[lab[v3 - 1]!]! ≠ hits[lab[v3 - 1 + 1]!]! := by
  have bounds := h.bounds
  rw [h.second _ (by omega) (by omega)]
  have hl := h.larger (v3 - 1 + 1) (by omega) (by omega)
  omega

end Minima

end Hex.GraphIso.Nauty.Sparse
