/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountOrder
public import HexGraphIso.Nauty.Sparse.CountRuns
public import HexGraphIso.Nauty.Sparse.NativeCounts
public import HexGraphIso.Nauty.Sparse.IndexTail

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Sorting an indirect segment orders its literal sequence of keys. -/
theorem Sort.Sorted.pairwise (h : Sort.Sorted lab hits first len) :
    ((segN lab first len).map fun v => hits[v]!).Pairwise (· ≤ ·) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hj' : j < len := by simpa only [List.length_map, segN_length] using hj
  simpa only [segN, List.getElem_map, List.getElem_range] using h i j hij hj'

/-- Equal key multisets have the same sorted key at every position,
even when equal-key vertices are reordered. -/
theorem Sort.Sorted.keys_eq
    (ha : Sort.Sorted lab hits first len) (hb : Sort.Sorted out keys first len)
    (hp : ((segN lab first len).map fun v => hits[v]!).Perm
      ((segN out first len).map fun v => keys[v]!))
    (hq : first ≤ q) (he : q < first + len) :
    hits[lab[q]!]! = keys[out[q]!]! := by
  have hlist := List.Perm.eq_of_pairwise (fun _ _ _ _ => Nat.le_antisymm)
    ha.pairwise hb.pairwise hp
  have hh := congrArg (fun l : List Nat => l[q - first]!) hlist
  have hq' : q - first < len := by omega
  simpa [segN, hq',
    show first + (q - first) = q by omega] using hh

/-- Equal count sequences determine the complete partition array written
by count splitting, including all unchanged exterior values. -/
theorem CountPartition.eq_ptn
    (ha : CountPartition level first last lab hits before ptn)
    (hb : CountPartition level first last out keys before other)
    (hk : ∀ q, first ≤ q → q ≤ last → hits[lab[q]!]! = keys[out[q]!]!) :
    ptn = other := by
  apply Array.ext (ha.size.trans hb.size.symm)
  intro q hq hr
  have he : ptn[q]! = other[q]! := by
    by_cases hlo : q < first
    · rw [ha.head q hlo, hb.head q hlo]
    · by_cases hhi : q < last
      · rw [ha.cuts q (by omega) hhi, hb.cuts q (by omega) hhi,
          hk q (by omega) (by omega), hk (q + 1) (by omega) (by omega)]
      · rw [ha.tail q (by omega), hb.tail q (by omega)]
  simpa only [getElem!_pos ptn q hq, getElem!_pos other q hr] using he

end Hex.GraphIso.Nauty.Sparse
