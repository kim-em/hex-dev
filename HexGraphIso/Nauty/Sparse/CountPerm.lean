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

/-- Installing fragments preserves the original cell's vertex multiset and
its exterior. The indirect sort stays inside the larger-count tail. -/
theorem CountSort.finish_window (level first last : Nat) (distance : Bool)
    (s : RefineSt n) (w1 v2 w2 v3 : Nat) (old : Array Nat)
    (h : Sort.Window old s.lab first last) (hf : first ≤ v3) (he : v3 ≤ last)
    (hb : last ≤ s.lab.size) :
    Sort.Window old (CountSort.finish level first last distance s w1 v2 w2 v3).lab
      first last := by
  rw [CountSort.finish_lab]
  split
  · exact h
  · split
    · exact h
    · exact h.indirect hf (by omega) hb

/-- Count splitting permutes exactly the selected cell and retains every
label outside it, without requiring bounds on the count values. -/
theorem splitCounts_window (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < s.lab.size) :
    Sort.Window s.lab (splitCounts level first distance s).lab first (s.cellend[first]! + 1) := by
  have hv := CountSort.firstRun_bounds s.lab s.hits first (s.cellend[first]! + 1) (by omega)
  have hm := CountSort.minima_window s.lab s.hits (n + 2) first (s.cellend[first]! + 1)
    (CountSort.firstRun s.lab s.hits first (s.cellend[first]! + 1)) hv.1 hv.2 (by omega)
  unfold splitCounts
  simp only [Id.run, bind, pure]
  split
  · exact .refl _ _ _
  · apply CountSort.finish_window
    · exact hm.1
    · have := hm.2; omega
    · exact hm.2.2.2
    · have := hm.1.size; dsimp only; omega

/-- The count splitter preserves the complete label permutation. -/
theorem splitCounts_perm (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < s.lab.size) :
    (splitCounts level first distance s).lab.toList.Perm s.lab.toList :=
  (splitCounts_window level first distance s hf hb).perm

end Hex.GraphIso.Nauty.Sparse
