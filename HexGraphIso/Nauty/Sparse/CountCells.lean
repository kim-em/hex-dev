/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountPerm
public import HexGraphIso.Nauty.Sparse.CountOutside
public import HexGraphIso.Nauty.Sparse.SortSegments
public import HexGraphIso.Nauty.Spec.CellPerm

public section

namespace Hex.GraphIso.Nauty.Sparse

theorem segN_extract (lab : Array Nat) (lo len : Nat) (hb : lo + len ≤ lab.size) :
    segN lab lo len = (lab.extract lo (lo + len)).toList := by
  apply List.ext_getElem
  · simp [segN]
    omega
  · intro i hi hj
    have hi' : i < len := by simpa only [segN_length] using hi
    simp only [segN, List.getElem_map, List.getElem_range, Array.getElem_toList,
      Array.getElem_extract]
    exact getElem!_pos lab (lo + i) (by omega)

/-- The cell's multiset of vertices survives its executed count split. -/
theorem splitCounts_segment (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < s.lab.size) :
    ((splitCounts level first distance s).lab.extract first (s.cellend[first]! + 1)).toList.Perm
      (s.lab.extract first (s.cellend[first]! + 1)).toList := by
  apply Sort.segment_perm ⟨by omega, by omega⟩ (splitCounts_perm level first distance s hf hb)
  intro q hq
  exact splitCounts_outside level first distance s hf hb q (by omega)

/-- Count splitting preserves the contents of every old partition cell.
The refined cells can be treated as subdivisions of the original cell. -/
theorem splitCounts_cells (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < s.lab.size)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first)) :
    cellsPerm s.ptn level (splitCounts level first distance s).lab s.lab := by
  intro a len ha
  have hp := splitCounts_perm level first distance s hf hb
  have hs := perm_size hp
  rcases isCell_disjoint_or_eq hc ha with hd | hd | ⟨rfl, rfl⟩
  · apply List.Perm.of_eq
    apply segN_congr
    intro i hi
    exact splitCounts_outside level first distance s hf hb (a + i) (by omega)
  · apply List.Perm.of_eq
    apply segN_congr
    intro i hi
    exact splitCounts_outside level first distance s hf hb (a + i) (by omega)
  · rw [segN_extract _ _ _ (by omega), segN_extract _ _ _ (by omega),
      show first + (s.cellend[first]! + 1 - first) = s.cellend[first]! + 1 by omega]
    exact splitCounts_segment level first distance s hf hb

end Hex.GraphIso.Nauty.Sparse
