/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Counts
public import HexGraphIso.Nauty.Sparse.TouchSort

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A neighbour scan couples first-touch generations with exact accumulated
counts. Its observation list includes skipped singleton neighbours. -/
structure CountScan (n stamp : Nat) (before marks touched starts hits : Array Nat)
    (seen : List Nat) : Prop where
  touch : Touched n stamp before marks touched (seen.map fun v => starts[v]!)
  counts : Counts n starts hits (seen.map fun v => starts[v]!) seen

namespace CountScan

variable {n stamp j : Nat} {before marks touched starts hits cleared : Array Nat} {seen : List Nat}

theorem initial (hm : Scratch.Marks n stamp before) (hs : hits.size = n) :
    CountScan n stamp before before #[] starts hits [] :=
  ⟨Touched.empty hm, Counts.initial hs⟩

theorem sentinel (h : CountScan n stamp before marks touched starts hits seen)
    (hj : starts[j]! = n) : CountScan n stamp before marks touched starts hits (seen ++ [j]) := by
  have ht := h.touch.sentinel
  have hc := h.counts.sentinel hj
  exact ⟨by simpa only [List.map_append, List.map_cons, List.map_nil, hj] using ht,
    by simpa only [List.map_append, List.map_cons, List.map_nil, hj] using hc⟩

theorem repeated (h : CountScan n stamp before marks touched starts hits seen)
    (hj : j < n) (hk : starts[j]! < n) (hm : marks[starts[j]!]! = stamp + 1) :
    CountScan n stamp before marks touched starts (hits.setIfInBounds j (hits[j]! + 1))
      (seen ++ [j]) := by
  have ht := h.touch.repeated hk hm
  have hc := (h.counts.repeated ((h.touch.marked hk).mp hm)).increment hj hk
    (List.mem_append_right _ (by simp))
  exact ⟨by simpa only [List.map_append, List.map_cons, List.map_nil] using ht,
    by simpa only [List.map_append, List.map_cons, List.map_nil] using hc⟩

theorem fresh (h : CountScan n stamp before marks touched starts hits seen)
    (hj : j < n) (hk : starts[j]! < n) (hm : marks[starts[j]!]! ≠ stamp + 1)
    (hs : cleared.size = n)
    (hz : ∀ v, v < n → cleared[v]! = if starts[v]! = starts[j]! then 0 else hits[v]!) :
    CountScan n stamp before (marks.setIfInBounds starts[j]! (stamp + 1))
      (touched.push starts[j]!) starts (cleared.setIfInBounds j (cleared[j]! + 1)) (seen ++ [j]) := by
  have ht := h.touch.fresh hk hm
  have hc := (h.counts.reset (fun hh => hm ((h.touch.marked hk).mpr hh)) hs hz).increment hj hk
    (List.mem_append_right _ (by simp))
  exact ⟨by simpa only [List.map_append, List.map_cons, List.map_nil] using ht,
    by simpa only [List.map_append, List.map_cons, List.map_nil] using hc⟩

theorem sorted (h : CountScan n stamp before marks touched starts hits seen) :
    CountScan n stamp before marks (sortCells touched) starts hits seen :=
  ⟨h.touch.sorted, h.counts⟩

end CountScan

end Hex.GraphIso.Nauty.Sparse
