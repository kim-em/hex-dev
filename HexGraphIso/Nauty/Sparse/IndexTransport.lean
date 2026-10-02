/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexVertex
public import HexGraphIso.Nauty.Sparse.ContextMap

public section

namespace Hex.GraphIso.Nauty.Sparse.Index.Valid

/-- Admissible vertex-to-cell caches commute with vertex renaming and
within-cell permutation, including the singleton sentinel. -/
theorem starts_map (σ : Renaming n)
    (hs : Index.Valid n lab ptn level starts ends)
    (ht : Index.Valid n out ptn level other final)
    (hp : lab.toList.Perm (List.range n)) (hsize : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level)
    (hcell : cellsPerm ptn level out (lab.map σ.toFun)) (hv : v < n) :
    other[σ v]! = starts[v]! := by
  have hl : lab.size = n := by simpa using hp.length_eq
  obtain ⟨q, hq, hqv⟩ := perm_position hp hv
  obtain ⟨a, len, hc, hb, hlo, hhi⟩ := Index.cover hsize hend hq
  have hmem : σ v ∈ segN out a len := by
    apply (hcell a len hc).mem_iff.mpr
    rw [segN_map_of_le _ _ _ _ (by omega)]
    apply List.mem_map.mpr
    refine ⟨v, mem_segN_iff.mpr ⟨q - a, by omega, ?_⟩, rfl⟩
    simpa only [Nat.add_sub_of_le hlo] using hqv
  obtain ⟨i, hi, he⟩ := mem_segN_iff.mp hmem
  rw [← he, ht.starts_eq a len hc hb (by omega) (a + i) (by omega) (by omega),
    ← hqv, hs.starts_eq a len hc hb (by omega) q hlo hhi]

/-- At cell starts, any two valid endpoint caches agree literally. Values
at other positions need not agree. -/
theorem ends_congr (hs : Index.Valid n lab ptn level starts ends)
    (ht : Index.Valid n out ptn level other final)
    (hc : IsCell ptn level a len) (hb : a + len ≤ n) : ends[a]! = final[a]! := by
  have hlen := hc.1
  rw [hs.ends_eq a len hc hb (by omega), ht.ends_eq a len hc hb (by omega)]

end Hex.GraphIso.Nauty.Sparse.Index.Valid
