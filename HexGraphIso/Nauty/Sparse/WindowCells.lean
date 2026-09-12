/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountCells
public import HexGraphIso.Nauty.Sparse.Window
public import HexGraphIso.Nauty.Sparse.Cuts

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A permutation confined to one complete cell preserves the multiset of
vertices in every old cell. -/
theorem Sort.Window.cells (h : Sort.Window before after first last)
    (hf : first ≤ last) (hb : last ≤ before.size)
    (hc : IsCell ptn level first (last - first)) : cellsPerm ptn level after before := by
  intro a len ha
  have hsize := h.size
  rcases isCell_disjoint_or_eq hc ha with ho | ho | ⟨he, he'⟩
  · apply List.Perm.of_eq
    apply segN_congr
    intro q hq
    exact h.outside (a + q) (by omega)
  · apply List.Perm.of_eq
    apply segN_congr
    intro q hq
    exact h.outside (a + q) (by omega)
  · subst a len
    rw [segN_extract _ _ _ (by omega), segN_extract _ _ _ (by omega), Nat.add_sub_cancel' hf]
    apply Sort.segment_perm ⟨by omega, by omega⟩ h.perm
    intro q hq
    exact h.outside q hq

/-- Cell permutations after refinement also preserve each original cell,
because every original closed boundary remains closed. -/
theorem Cuts.perm {n level old count upto : Nat} {before ptn lab out : Array Nat}
    (h : Cuts level n before ptn old count upto)
    (hp : before.size = n) (hl : lab.size = n) (ho : out.size = n)
    (hend : before[n - 1]! ≤ level) (hc : cellsPerm ptn level out lab) :
    cellsPerm before level out lab := by
  have hsize := h.size
  apply cellsPerm_coarsen h.size.symm (by omega) (by omega) hc
  · rw [h.size, hp, h.closed _ hend]
    exact hend
  · simpa only [hp] using hend
  · intro q hq
    rw [h.closed q hq]
    exact hq

end Hex.GraphIso.Nauty.Sparse
