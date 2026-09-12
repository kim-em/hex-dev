/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountPartition
public import HexGraphIso.Nauty.Sparse.CountPattern
public import HexGraphIso.Nauty.Spec.CellPerm

public section

namespace Hex.GraphIso.Nauty.Sparse.CountPartition

/-- Within an original cell, a new cell consists of one maximal run of
equal counts. The two ends use the original boundaries or a count change. -/
theorem cell_iff (h : CountPartition level first last lab hits before ptn)
    (hc : IsCell before level first (last + 1 - first))
    (ha : first ≤ a) (hlen : 0 < len) (hb : a + len ≤ last + 1) :
    IsCell ptn level a len ↔
      (a = first ∨ hits[lab[a - 1]!]! ≠ hits[lab[a]!]!) ∧
      (∀ q, a ≤ q → q < a + len → hits[lab[q]!]! = hits[lab[a]!]!) ∧
      (a + len - 1 = last ∨ hits[lab[a + len - 1]!]! ≠ hits[lab[a + len]!]!) := by
  have hf : first ≤ last := by have := hc.1; omega
  have hopen (q : Nat) (hq : first ≤ q) (hl : q < last) : level < before[q]! :=
    hc.2.2.1 q hq (by omega)
  have hend : before[last]! ≤ level := by
    simpa only [show first + (last + 1 - first) - 1 = last by omega] using hc.2.2.2
  have left : (a = 0 ∨ ptn[a - 1]! ≤ level) ↔
      (a = first ∨ hits[lab[a - 1]!]! ≠ hits[lab[a]!]!) := by
    by_cases he : a = first
    · subst a
      have hx : first = 0 ∨ ptn[first - 1]! ≤ level := by
        rcases hc.2.1 with hz | hz
        · exact Or.inl hz
        · by_cases hf0 : first = 0
          · exact Or.inl hf0
          · exact Or.inr (by rw [h.head _ (by omega)]; exact hz)
      simp only [hx, true_or]
    · have hp := h.cuts (a - 1) (by omega) (by omega)
      have ho := hopen (a - 1) (by omega) (by omega)
      rw [show a - 1 + 1 = a by omega] at hp
      rw [hp]
      by_cases hk : hits[lab[a - 1]!]! = hits[lab[a]!]! <;> simp only [hk, ite_true, ite_false]
      · constructor <;> intro hh <;> omega
      · constructor <;> intro hh
        · exact Or.inr hk
        · exact Or.inr (Nat.le_refl _)
  have right : ptn[a + len - 1]! ≤ level ↔
      (a + len - 1 = last ∨ hits[lab[a + len - 1]!]! ≠ hits[lab[a + len]!]!) := by
    by_cases he : a + len - 1 = last
    · rw [he, h.tail last (Nat.le_refl _)]
      simp only [hend, true_or, iff_self]
    · have hp := h.cuts (a + len - 1) (by omega) (by omega)
      have ho := hopen (a + len - 1) (by omega) (by omega)
      rw [show a + len - 1 + 1 = a + len by omega] at hp
      rw [hp]
      by_cases hk : hits[lab[a + len - 1]!]! = hits[lab[a + len]!]! <;>
        simp only [hk, ite_true, ite_false]
      · constructor <;> intro hh <;> omega
      · constructor <;> intro hh
        · exact Or.inr hk
        · exact Nat.le_refl _
  have middle : (∀ q, a ≤ q → q + 1 < a + len → level < ptn[q]!) ↔
      (∀ q, a ≤ q → q < a + len → hits[lab[q]!]! = hits[lab[a]!]!) := by
    constructor
    · intro hi
      have adjacent (q : Nat) (hq : a ≤ q) (hl : q + 1 < a + len) :
          hits[lab[q]!]! = hits[lab[q + 1]!]! := by
        have hp := h.cuts q (by omega) (by omega)
        have hg := hi q hq hl
        split at hp
        · assumption
        · omega
      have all (i : Nat) (hi : i < len) : hits[lab[a + i]!]! = hits[lab[a]!]! := by
        induction i with
        | zero => simp
        | succ i ih =>
          rw [show a + (i + 1) = a + i + 1 by omega,
            ← adjacent (a + i) (by omega) (by omega)]
          exact ih (by omega)
      intro q hq hl
      have hv := all (q - a) (by omega)
      simpa only [show a + (q - a) = q by omega] using hv
    · intro hi q hq hl
      rw [h.cuts q (by omega) (by omega), hi q hq (by omega),
        hi (q + 1) (by omega) hl, ite_eq_left rfl]
      exact hopen q (by omega) (by omega)
  simp only [IsCell, hlen, true_and, left, middle, right]

/-- A count split only subdivides its original cell. Every output cell is
before it, after it, or contained in it. -/
theorem nesting (h : CountPartition level first last lab hits before ptn)
    (hc : IsCell before level first (last + 1 - first))
    (ho : IsCell ptn level a len) :
    a + len ≤ first ∨ last < a ∨ (first ≤ a ∧ a + len ≤ last + 1) := by
  have hf : first ≤ last := by have := hc.1; omega
  by_cases hleft : a + len ≤ first
  · exact Or.inl hleft
  · apply Or.inr
    by_cases hright : last < a
    · exact Or.inl hright
    · apply Or.inr
      constructor
      · by_cases ha : first ≤ a
        · exact ha
        · have hx := ho.2.2.1 (first - 1) (by omega) (by omega)
          rw [h.head _ (by omega)] at hx
          rcases hc.2.1 with hh | hh <;> omega
      · by_cases he : a + len ≤ last + 1
        · exact he
        · have hx := ho.2.2.1 last (by omega) (by omega)
          rw [h.tail last (Nat.le_refl _)] at hx
          have hh := hc.2.2.2
          have heq : first + (last + 1 - first) - 1 = last := by omega
          rw [heq] at hh
          omega

/-- Cells outside the split retain their original partition data. -/
theorem cell_outside (h : CountPartition level first last lab hits before ptn)
    (hc : IsCell ptn level a len) (hd : a + len ≤ first ∨ last < a) :
    IsCell before level a len := by
  have hp := hc.1
  have get (q : Nat) (hq : a - 1 ≤ q) (he : q < a + len) : ptn[q]! = before[q]! := by
    rcases hd with hd | hd
    · exact h.head q (by omega)
    · exact h.tail q (by omega)
  refine ⟨hp, ?_, ?_, ?_⟩
  · rcases hc.2.1 with hz | hz
    · exact Or.inl hz
    · exact Or.inr (by rw [← get _ (by omega) (by omega)]; exact hz)
  · intro q hq he
    rw [← get q (by omega) (by omega)]
    exact hc.2.2.1 q hq he
  · rw [← get _ (by omega) (by omega)]
    exact hc.2.2.2

end Hex.GraphIso.Nauty.Sparse.CountPartition

namespace Hex.GraphIso.Nauty.Sparse

/-- The actual count splitter's cells are exactly the maximal equal-count
runs inside the incoming cell. -/
theorem splitCounts_cell_iff (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hb : s.cellend[first]! < n)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (ha : first ≤ a) (hlen : 0 < len) (he : a + len ≤ s.cellend[first]! + 1) :
    let lab := (splitCounts level first distance s).lab
    IsCell (splitCounts level first distance s).ptn level a len ↔
      (a = first ∨ s.hits[lab[a - 1]!]! ≠ s.hits[lab[a]!]!) ∧
      (∀ q, a ≤ q → q < a + len → s.hits[lab[q]!]! = s.hits[lab[a]!]!) ∧
      (a + len - 1 = s.cellend[first]! ∨
        s.hits[lab[a + len - 1]!]! ≠ s.hits[lab[a + len]!]!) := by
  have hf : first ≤ s.cellend[first]! := by have := hc.1; omega
  exact (splitCounts_partition level first distance s hl hs hf hb hk).cell_iff hc ha hlen he

end Hex.GraphIso.Nauty.Sparse
