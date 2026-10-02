/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CompactKeys
public import HexGraphIso.Nauty.Sparse.IndexWrites

public section

namespace Hex.GraphIso.Nauty.Sparse.Fill

/-- In a valid labelling, a copied vertex occurs in the copied interval and
nowhere else. -/
theorem mem_iff (h : Fill before data first data.length after)
    (hp : after.toList.Perm (List.range n)) (hq : q < n) :
    after[q]! ∈ data ↔ first ≤ q ∧ q < first + data.length := by
  have hs : after.size = n := by simpa using hp.length_eq
  have fits := h.fits
  constructor
  · intro hm
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    have hr := h.read (q := first + i) (by omega) (by omega)
    simp only [Nat.add_sub_cancel_left, getElem!_pos data i hi] at hr
    have hh := perm_injective hp hq (show first + i < n by have := h.size; omega)
      (he.symm.trans hr.symm)
    omega
  · intro hb
    rw [h.read hb.1 hb.2, getElem!_pos data (q - first) (by omega)]
    exact List.getElem_mem _

/-- The vertex writes of reverse reinsertion are exactly a scatter along the
completed label interval. -/
theorem scatter (h : Fill before data first data.length after)
    (hp : after.toList.Perm (List.range n))
    (hw : Index.Writes n starts out data value) :
    Index.Scatter n after starts out first (first + data.length) value := by
  refine ⟨hw.size, ?_⟩
  intro q hq
  rw [hw.get _ (perm_bound hp hq)]
  simp only [h.mem_iff hp hq]

end Hex.GraphIso.Nauty.Sparse.Fill
