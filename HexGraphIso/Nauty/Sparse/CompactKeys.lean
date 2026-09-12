/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CompactFinish

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Read a copied list after a fixed array prefix. -/
theorem prefix_read {lab : Array Nat} {pre data : List Nat} {upto q : Nat}
    (h : lab.toList.take upto = pre ++ data) (hq : pre.length ≤ q)
    (hu : q < upto) (hb : q < lab.size) : lab[q]! = data[q - pre.length]! := by
  have hh := congrArg (fun xs : List Nat => xs[q]?) h
  rw [List.getElem?_take_of_lt hu, List.getElem?_append_right hq] at hh
  have hl := congrArg List.length h
  simp only [List.length_take, Array.length_toList, List.length_append] at hl
  have hd : q - pre.length < data.length := by omega
  rw [List.getElem?_eq_getElem (by simpa using hb), List.getElem?_eq_getElem hd] at hh
  simpa only [getElem!_pos lab q hb, getElem!_pos data (q - pre.length) hd,
    Array.getElem_toList] using Option.some.inj hh

namespace Fill

theorem read (h : Fill before data first upto after) (hq : first ≤ q) (hu : q < first + upto) :
    after[q]! = data[q - first]! := by
  have fits := h.fits
  have bound := h.bound
  have hh := prefix_read h.copied (q := q) (by simp only [List.length_take, Array.length_toList]; omega)
    hu (by rw [h.size]; omega)
  simp only [List.length_take, Array.length_toList, Nat.min_eq_left (show first ≤ before.size by omega)] at hh
  rw [hh]
  simp only [getElem!_def, List.getElem?_take_of_lt (show q - first < upto by omega)]

end Fill

namespace Compact

/-- Every vertex retained by compaction fails the split predicate. -/
theorem retained (h : Compact before p first upto seen lab hit next)
    (hq : first ≤ q) (hu : q < next) : p lab[q]! = false := by
  have bounds := h.bounds
  have hc := h.count
  have hh := prefix_read h.kept (q := q) (by simp only [List.length_take, Array.length_toList]; omega)
    hu (by rw [h.size]; omega)
  simp only [List.length_take, Array.length_toList, Nat.min_eq_left (show first ≤ before.size by omega)] at hh
  rw [hh]
  have hi : q - first < (seen.filter fun v => !p v).length := by omega
  have hm : (seen.filter fun v => !p v)[q - first]! ∈ seen.filter (fun v => !p v) := by
    rw [getElem!_pos (seen.filter fun v => !p v) (q - first) hi]
    exact List.getElem_mem _
  simpa using (List.mem_filter.mp hm).2

/-- Reinsertion produces the two predicate classes in the required order. -/
theorem separated (h : Compact before p first last seen lab hit next)
    (hlen : seen.length = last - first)
    (hr : Fill lab hit.toList.reverse next hit.toList.reverse.length out) :
    (∀ q, first ≤ q → q < next → p out[q]! = false) ∧
      (∀ q, next ≤ q → q < last → p out[q]! = true) := by
  have hextent := h.extent hlen
  refine ⟨?_, ?_⟩
  · intro q hq hu
    rw [hr.exterior q (Or.inl hu)]
    exact h.retained hq hu
  · intro q hq hu
    have hi : q - next < hit.toList.reverse.length := by
      simp only [List.length_reverse, Array.length_toList]
      omega
    rw [hr.read hq (by simp only [List.length_reverse, Array.length_toList]; omega)]
    have hm : hit.toList.reverse[q - next]! ∈ hit.toList.reverse := by
      rw [getElem!_pos hit.toList.reverse (q - next) hi]
      exact List.getElem_mem _
    rw [List.mem_reverse, h.hits] at hm
    simpa only [h.hits] using (List.mem_filter.mp hm).2

end Compact

end Hex.GraphIso.Nauty.Sparse
