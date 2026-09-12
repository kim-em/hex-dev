/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountValid
public import HexGraphIso.Nauty.Sparse.CountFrame
public import HexGraphIso.Nauty.Sparse.CountOutside

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A count split retains the full partition contract of a disjoint cell. -/
theorem CountPartition.preserve (h : CountPartition level first last lab hits before ptn)
    (hc : IsCell before level a len) (hd : a + len ≤ first ∨ last < a) :
    IsCell ptn level a len := by
  have hp := hc.1
  have get (q : Nat) (hq : a - 1 ≤ q) (he : q < a + len) : ptn[q]! = before[q]! := by
    rcases hd with hd | hd
    · exact h.head q (by omega)
    · exact h.tail q (by omega)
  refine ⟨hp, ?_, ?_, ?_⟩
  · rcases hc.2.1 with hz | hz
    · exact Or.inl hz
    · exact Or.inr (by rw [get _ (by omega) (by omega)]; exact hz)
  · intro q hq he
    rw [get q (by omega) (by omega)]
    exact hc.2.2.1 q hq he
  · rw [get _ (by omega) (by omega)]
    exact hc.2.2.2

/-- Splitting one touched cell preserves the partition and local hit bound
of every other pending cell. -/
theorem splitCounts_other (level first a len limit : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hs : s.ptn.size = n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < n)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (ha : IsCell s.ptn level a len) (hne : a ≠ first)
    (hh : ∀ q, a ≤ q → q < a + len → s.hits[s.lab[q]!]! ≤ limit) :
    let t := splitCounts level first distance s
    IsCell t.ptn level a len ∧ ∀ q, a ≤ q → q < a + len → t.hits[t.lab[q]!]! ≤ limit := by
  have hd : a + len ≤ first ∨ s.cellend[first]! < a := by
    rcases isCell_disjoint_or_eq hc ha with ho | ho | he
    · exact Or.inl ho
    · right; omega
    · exact False.elim (hne he.1.symm)
  refine ⟨(splitCounts_partition level first distance s hl hs hf hb hk).preserve ha hd, ?_⟩
  intro q hq hu
  rw [(splitCounts_frame level first distance s).hits,
    splitCounts_outside level first distance s hf (by omega) q (by omega)]
  exact hh q hq hu

end Hex.GraphIso.Nauty.Sparse
