/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexVertex
public import HexGraphIso.Nauty.Sparse.NativeCounts

public section

namespace Hex.GraphIso.Nauty.Sparse.Index.Valid

/-- A native vertex-to-cell lookup tests membership in the corresponding
nontrivial cell's vertex set. Singleton sentinels cannot match that start. -/
theorem mem_cell {n level a len v : Nat} {lab ptn starts ends : Array Nat}
    (h : Index.Valid n lab ptn level starts ends) (hp : lab.toList.Perm (List.range n))
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hc : IsCell ptn level a len) (hb : a + len ≤ n) (hn : 1 < len) (hv : v < n) :
    (starts[v]! == a) = (worksetOf n lab a (a + len - 1)).mem v := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, mem_worksetOf_iff]
  constructor
  · intro he
    obtain ⟨q, hq, heq⟩ := perm_position hp hv
    have hi := h.nontrivial hs hend hq (by rw [heq, he]; omega)
    have hends := h.ends_eq a len hc hb (by omega)
    simp only [heq, he, hends] at hi
    refine ⟨hv, mem_segN_iff.mpr ⟨q - a, by omega, ?_⟩⟩
    rwa [Nat.add_sub_of_le hi.2.2.2.1]
  · rintro ⟨_, hm⟩
    obtain ⟨o, ho, he⟩ := mem_segN_iff.mp hm
    have hi := h.starts_eq a len hc hb (by omega) (a + o) (by omega) (by omega)
    rw [ite_eq_right (by omega : len ≠ 1)] at hi
    rwa [he] at hi

end Hex.GraphIso.Nauty.Sparse.Index.Valid
