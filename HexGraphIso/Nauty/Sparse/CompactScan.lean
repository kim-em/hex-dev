/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CompactIndex

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Reading the bounded native interval gives exactly its list slice. -/
theorem array_slice (a : Array Nat) {lo hi : Nat} (hlo : lo ≤ hi)
    (hhi : hi ≤ a.size) :
    ((List.range' lo (hi - lo)).map fun e => a[e]!) =
      (a.toList.drop lo).take (hi - lo) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range', List.length_take,
      List.length_drop, Array.length_toList]
    omega
  · intro i hi' hj
    have hb : lo + i < a.size := by simp only [List.length_map, List.length_range'] at hi'; omega
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul, List.getElem_take,
      List.getElem_drop, Array.getElem_toList, getElem!_pos a (lo + i) hb]

namespace Compact

/-- The hit buffer inherits the original labelling's vertex bounds. -/
theorem hit_bound (h : Compact before p first last seen lab hit cut)
    (hv : ∀ v ∈ seen, v < n) : ∀ v ∈ hit.toList, v < n := by
  intro v hm
  rw [h.hits] at hm
  exact hv v (List.mem_filter.mp hm).1

/-- A completed scan can be read directly as the original cell slice. -/
theorem scan_slice (h : Compact before p first (first + (last - first))
    ((List.range' first (last - first)).map fun q => before[q]!) lab hit cut)
    (hf : first ≤ last) :
    Compact before p first last ((before.toList.drop first).take (last - first)) lab hit cut := by
  have hb := h.bounds
  simpa only [Nat.add_sub_cancel' hf, array_slice before hf (by omega)] using h

/-- Compaction and reinsertion preserve every other cell, independently of
which singleton sentinel or activation branch follows the scan. -/
theorem preserve (h : Compact before p first last seen lab hit cut)
    (hc : IsCell ptn level first (last - first))
    (ha : IsCell ptn level a len) (hne : a ≠ first) :
    IsCell (if cut ≠ last ∧ cut ≠ first then ptn.setIfInBounds (cut - 1) level else ptn)
      level a len := by
  by_cases hd : cut ≠ last ∧ cut ≠ first
  · rw [ite_eq_left hd]
    have bounds := h.bounds
    apply CellCut.preserve (first := first) (last := last) ha (by omega) (by omega)
    rcases isCell_disjoint_or_eq hc ha with ho | ho | he
    · exact Or.inl ho
    · right; omega
    · exact False.elim (hne he.1.symm)
  · simpa only [ite_eq_right hd] using ha

end Compact

end Hex.GraphIso.Nauty.Sparse
