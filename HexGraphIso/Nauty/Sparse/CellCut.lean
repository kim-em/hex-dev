/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Spec.CellPerm

public section

namespace Hex.GraphIso.Nauty.Sparse.CellCut

variable {ptn : Array Nat} {level first cut last a len : Nat}

theorem left (h : IsCell ptn level first (last - first)) (hf : first < cut) (hl : cut < last)
    (hb : cut - 1 < ptn.size) :
    IsCell (ptn.setIfInBounds (cut - 1) level) level first (cut - first) := by
  change IsCell (ptn.set! (cut - 1) level) level first (cut - first)
  refine ⟨by omega, ?_, ?_, ?_⟩
  · by_cases h0 : first = 0
    · exact Or.inl h0
    · right
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      exact h.2.1.resolve_left h0
  · intro q hq hu
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact h.2.2.1 q hq (by omega)
  · rw [show first + (cut - first) - 1 = cut - 1 by omega,
      Array.getElem!_set!_self _ _ _ hb]
    exact Nat.le_refl _

theorem right (h : IsCell ptn level first (last - first)) (hf : first < cut) (hl : cut < last)
    (hb : cut - 1 < ptn.size) :
    IsCell (ptn.setIfInBounds (cut - 1) level) level cut (last - cut) := by
  change IsCell (ptn.set! (cut - 1) level) level cut (last - cut)
  refine ⟨by omega, Or.inr ?_, ?_, ?_⟩
  · rw [Array.getElem!_set!_self _ _ _ hb]
    exact Nat.le_refl _
  · intro q hq hu
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact h.2.2.1 q (by omega) (by omega)
  · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    simpa only [show cut + (last - cut) - 1 = first + (last - first) - 1 by omega] using h.2.2.2

/-- A cut leaves every disjoint cell's boundary values unchanged. -/
theorem outside (h : IsCell (ptn.setIfInBounds (cut - 1) level) level a len)
    (hf : first < cut) (hl : cut < last) (ho : a + len ≤ first ∨ last ≤ a) :
    IsCell ptn level a len := by
  change IsCell (ptn.set! (cut - 1) level) level a len at h
  have hpos := h.1
  refine ⟨hpos, ?_, ?_, ?_⟩
  · rcases h.2.1 with h0 | hs
    · exact Or.inl h0
    · right
      rwa [Array.getElem!_set!_ne _ _ _ _ (by omega)] at hs
  · intro q hq hu
    have hh := h.2.2.1 q hq hu
    rwa [Array.getElem!_set!_ne _ _ _ _ (by omega)] at hh
  · have hh := h.2.2.2
    rwa [Array.getElem!_set!_ne _ _ _ _ (by omega)] at hh

/-- A cut inside one cell preserves the partition contract of every disjoint
cell, including its open interior and both closed endpoints. -/
theorem preserve (h : IsCell ptn level a len)
    (hf : first < cut) (hl : cut < last) (ho : a + len ≤ first ∨ last ≤ a) :
    IsCell (ptn.setIfInBounds (cut - 1) level) level a len := by
  change IsCell (ptn.set! (cut - 1) level) level a len
  have hpos := h.1
  refine ⟨hpos, ?_, ?_, ?_⟩
  · rcases h.2.1 with h0 | hs
    · exact Or.inl h0
    · right
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      exact hs
  · intro q hq hu
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact h.2.2.1 q hq hu
  · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact h.2.2.2

/-- One boundary write replaces precisely its original cell by the two
fragments; all other cells retain their original boundary contract. -/
theorem cells (h : IsCell ptn level first (last - first)) (hf : first < cut) (hl : cut < last)
    (hb : cut - 1 < ptn.size)
    (ha : IsCell (ptn.setIfInBounds (cut - 1) level) level a len) :
    ((a + len ≤ first ∨ last ≤ a) ∧ IsCell ptn level a len) ∨
      (a = first ∧ len = cut - first) ∨ (a = cut ∧ len = last - cut) := by
  have hpos := ha.1
  rcases isCell_disjoint_or_eq (left h hf hl hb) ha with ho | ho | ⟨he, he'⟩
  · exact Or.inl ⟨Or.inl ho, outside ha hf hl (Or.inl ho)⟩
  · rcases isCell_disjoint_or_eq (right h hf hl hb) ha with ho' | ho' | ⟨he, he'⟩
    · omega
    · have hh : last ≤ a := by omega
      exact Or.inl ⟨Or.inr hh, outside ha hf hl (Or.inr hh)⟩
    · exact Or.inr (Or.inr ⟨he.symm, he'.symm⟩)
  · exact Or.inr (Or.inl ⟨he.symm, he'.symm⟩)

end Hex.GraphIso.Nauty.Sparse.CellCut
