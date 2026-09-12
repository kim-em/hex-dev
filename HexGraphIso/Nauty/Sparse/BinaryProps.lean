/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BinaryEquiv

public section

namespace Hex.GraphIso.Nauty.Sparse.Binary

/-- Processing one cell preserves every other cell's partition boundaries. -/
theorem Cell.preserve (h : Cell level first last pred s t)
    (hc : IsCell s.ptn level first (last - first))
    (ha : IsCell s.ptn level a len) (hne : a ≠ first) : IsCell t.ptn level a len := by
  have hlen := hc.1
  have bounds := cut_bounds s.lab pred (by omega : first ≤ last)
  rw [h.ptn]
  by_cases hd : cut s.lab pred first last ≠ last ∧ cut s.lab pred first last ≠ first
  · rw [ite_eq_left hd]
    apply CellCut.preserve (first := first) (last := last) ha (by omega) (by omega)
    rcases isCell_disjoint_or_eq hc ha with ho | ho | he
    · exact Or.inl ho
    · right; omega
    · exact False.elim (hne he.1.symm)
  · simpa only [ite_eq_right hd] using ha

/-- The next cell receives a labelling permutation, allocated partition and
valid cache from the preceding executed cell body. -/
theorem Cell.valid {s t : RefineSt n} (h : Cell level first last pred s t)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hc : IsCell s.ptn level first (last - first)) (hn : first + 1 < last) :
    t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
      Index.Valid n t.lab t.ptn level t.cellstart t.cellend :=
  ⟨h.window.perm.trans hp, h.frame.ptn_size.trans hs, h.cache hp hs hi hc hn⟩

end Hex.GraphIso.Nauty.Sparse.Binary
