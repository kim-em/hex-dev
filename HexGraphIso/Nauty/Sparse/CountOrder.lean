/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine.Minima
public import HexGraphIso.Nauty.Sparse.CountFinish

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Installing the minimum-count fragments and sorting their tail orders
the entire cell. Index, queue and hash updates preserve that label array. -/
theorem CountSort.finish_sorted (level first last : Nat) (distance : Bool)
    (s : RefineSt n) (w1 v2 w2 v3 : Nat)
    (h : Minima s.lab s.hits first v2 v3 last w1 w2) (hb : last ≤ s.lab.size) :
    Sort.Sorted (CountSort.finish level first last distance s w1 v2 w2 v3).lab
      s.hits first (last - first) := by
  rw [CountSort.finish_lab]
  split
  · next he => exact h.done_sorted (Or.inl he)
  · split
    · next he => exact h.done_sorted (Or.inr he)
    · exact h.sort_tail hb

/-- Count splitting orders the whole cell by its hit values. Only the
initial key must lie below the second-minimum sentinel. -/
theorem splitCounts_sorted (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < s.lab.size)
    (hk : s.hits[s.lab[first]!]! < n + 2) :
    Sort.Sorted (splitCounts level first distance s).lab s.hits first
      (s.cellend[first]! + 1 - first) := by
  have hv := CountSort.firstRun_spec s.lab s.hits first (s.cellend[first]! + 1) (by omega)
  have hm := CountSort.minima_spec s.lab s.hits (n + 2) first (s.cellend[first]! + 1)
    (CountSort.firstRun s.lab s.hits first (s.cellend[first]! + 1))
    hv.1 hv.2.1 (by omega) hk hv.2.2.1
  unfold splitCounts
  simp only [Id.run, bind, pure]
  split
  · next he =>
    simp only [beq_iff_eq] at he
    apply Minima.constant_sorted (value := s.hits[s.lab[first]!]!)
    simpa only [he, RefineSt.hash] using hv.2.2.1
  · apply CountSort.finish_sorted
    · exact hm.1
    · dsimp only; rw [hm.2]; omega

end Hex.GraphIso.Nauty.Sparse
