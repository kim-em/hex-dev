/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexProps
public import HexGraphIso.Nauty.Sparse.Window

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every vertex has a position in a labelling permutation. -/
theorem perm_position {lab : Array Nat} {n v : Nat} (hp : lab.toList.Perm (List.range n)) (hv : v < n) :
    ∃ q, q < n ∧ lab[q]! = v := by
  have hl : lab.size = n := by simpa using hp.length_eq
  have hm : v ∈ lab.toList := hp.mem_iff.mpr (List.mem_range.mpr hv)
  obtain ⟨q, hq, he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨q, by simp only [Array.length_toList] at hq; omega, ?_⟩
  simpa only [Array.getElem_toList, getElem!_pos lab q (by simpa using hq)] using he

namespace Index.Valid

/-- Native vertex lookup is bounded even when the caller has no inverse label
array; the singleton sentinel is the only permitted value equal to `n`. -/
theorem vertex_le {lab ptn starts ends : Array Nat} {n level v : Nat}
    (h : Index.Valid n lab ptn level starts ends) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (hp : lab.toList.Perm (List.range n)) (hv : v < n) :
    starts[v]! ≤ n := by
  obtain ⟨q, hq, he⟩ := perm_position hp hv
  simpa only [he] using h.start_le hs hend hq

/-- Every nonsentinel native vertex lookup identifies a bounded nontrivial
cell, providing the bounds used by first-touch clearing. -/
theorem vertex_cell {lab ptn starts ends : Array Nat} {n level v : Nat}
    (h : Index.Valid n lab ptn level starts ends) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (hp : lab.toList.Perm (List.range n)) (hv : v < n)
    (hne : starts[v]! ≠ n) :
    let a := starts[v]!
    let b := ends[a]!
    IsCell ptn level a (b + 1 - a) ∧ a < b ∧ b < n := by
  obtain ⟨q, hq, he⟩ := perm_position hp hv
  have hh := h.nontrivial hs hend hq (by simpa only [he] using hne)
  simpa only [he] using And.intro hh.1 (And.intro hh.2.1 hh.2.2.1)

end Index.Valid

end Hex.GraphIso.Nauty.Sparse
