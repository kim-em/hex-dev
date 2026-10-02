/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountBound
public import HexGraphIso.Nauty.Sparse.CountConstant

public section

namespace Hex.GraphIso.Nauty.Sparse.CountScan

variable {n stamp v : Nat} {before marks touched starts hits : Array Nat} {seen : List Nat}

/-- Counts in a touched nontrivial cell interpret the native neighbour scan. -/
theorem read (h : CountScan n stamp before marks touched starts hits seen)
    (hv : v < n) (ht : starts[v]! ∈ touched.toList) : hits[v]! = seen.count v := by
  have hm := (h.touch.members _).mp ht
  exact h.counts.get v hv hm.1 hm.2

/-- Untouched nontrivial cells have zero semantic count, regardless of their
retained scratch values. They therefore need no count split. -/
theorem zero (h : CountScan n stamp before marks touched starts hits seen)
    (hk : starts[v]! < n) (ht : starts[v]! ∉ touched.toList) : seen.count v = 0 := by
  apply List.count_eq_zero.mpr
  intro hv
  exact ht ((h.touch.members _).mpr ⟨hk, List.mem_map.mpr ⟨v, hv, rfl⟩⟩)

/-- The valid cache supplies the semantic key on every vertex of a touched
cell, which is precisely the hypothesis used by `splitCounts_constant`. -/
theorem cell_key (h : CountScan n stamp before marks touched starts hits seen)
    {lab ptn ends : Array Nat} {level first len : Nat}
    (hp : lab.toList.Perm (List.range n))
    (hi : Index.Valid n lab ptn level starts ends)
    (hc : IsCell ptn level first len) (hl : 1 < len) (hb : first + len ≤ n)
    (ht : first ∈ touched.toList) :
    ∀ v ∈ segN lab first len, hits[v]! = seen.count v := by
  intro v hv
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
  have hq := List.mem_range.mp hq
  have he := hi.starts_eq first len hc hb (by omega) (first + q) (by omega) (by omega)
  rw [ite_eq_right (by omega)] at he
  apply h.read (perm_bound hp (by omega))
  rwa [he]

/-- Every vertex of an untouched nontrivial cell has zero native count. -/
theorem cell_zero (h : CountScan n stamp before marks touched starts hits seen)
    {lab ptn ends : Array Nat} {level first len : Nat}
    (hi : Index.Valid n lab ptn level starts ends)
    (hc : IsCell ptn level first len) (hl : 1 < len) (hb : first + len ≤ n)
    (ht : first ∉ touched.toList) :
    ∀ v ∈ segN lab first len, seen.count v = 0 := by
  intro v hv
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
  have hq := List.mem_range.mp hq
  have he := hi.starts_eq first len hc hb (by omega) (first + q) (by omega) (by omega)
  rw [ite_eq_right (by omega)] at he
  apply h.zero
  · rw [he]; omega
  · rwa [he]

end Hex.GraphIso.Nauty.Sparse.CountScan
