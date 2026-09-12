/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexTail
public import HexGraphIso.Nauty.Sparse.MinimaPerm

public section

namespace Hex.GraphIso.Nauty.Sparse.Index

/-- The cache describes every count run and retains entries outside the
original cell. Label permutation is retained for subsequent cache accesses. -/
structure Complete (n first last : Nat) (oldlab hits oldstarts oldends : Array Nat)
    (s : RefineSt n) : Prop where
  window : Sort.Window oldlab s.lab first (last + 1)
  runs : Runs n first last (last + 1) s.lab hits s.cellstart s.cellend
  frame : Frame n first last oldlab s.lab oldstarts s.cellstart oldends s.cellend

namespace Complete

theorem iff : Complete n first last oldlab hits oldstarts oldends s ↔
    Sort.Window oldlab s.lab first (last + 1) ∧
    Runs n first last (last + 1) s.lab hits s.cellstart s.cellend ∧
    Frame n first last oldlab s.lab oldstarts s.cellstart oldends s.cellend :=
  ⟨fun h => ⟨h.window, h.runs, h.frame⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

theorem of_tail (h : Tail n first last last oldlab hits oldstarts oldends s) :
    Complete n first last oldlab hits oldstarts oldends s := ⟨h.window, h.runs, h.frame⟩

theorem transfer (h : Complete n first last oldlab hits oldstarts oldends s)
    (hl : t.lab = s.lab) (hs : t.cellstart = s.cellstart) (he : t.cellend = s.cellend) :
    Complete n first last oldlab hits oldstarts oldends t := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hl] using h.window
  · simpa only [hl, hs, he] using h.runs
  · simpa only [hl, hs, he] using h.frame

/-- A constant cell leaves its original endpoint and vertex indices valid,
including the singleton sentinel. A within-cell permutation is harmless. -/
theorem constant (hw : Sort.Window oldlab s.lab first (last + 1))
    (hs : s.cellstart = oldstarts) (he : s.cellend = oldends)
    (hss : oldstarts.size = n) (hes : oldends.size = n)
    (hl : last < s.lab.size) (hf : first ≤ last) (hend : oldends[first]! = last)
    (hv : ∀ q, first ≤ q → q ≤ last →
      oldstarts[oldlab[q]!]! = if first = last then n else first)
    (hk : ∀ q, first ≤ q → q ≤ last → hits[s.lab[q]!]! = value) :
    Complete n first last oldlab hits oldstarts oldends s := by
  have hr : Run s.lab hits first last first last := by
    refine ⟨by omega, Or.inl rfl, ?_, Or.inl rfl⟩
    intro q hq hq'
    rw [hk q hq hq', hk first (Nat.le_refl _) hf]
  refine ⟨hw, ?_, ?_⟩
  · refine ⟨by simpa [hs], by simpa [he], ?_, ?_⟩
    · intro a b ha hb
      have bounds := ha.bounds
      rcases hr.disjoint_or_eq ha with hh | hh | ⟨rfl, rfl⟩
      · omega
      · omega
      · simpa only [he] using hend
    · intro a b ha hb q hq hq'
      have bounds := ha.bounds
      rcases hr.disjoint_or_eq ha with hh | hh | ⟨rfl, rfl⟩
      · omega
      · omega
      · obtain ⟨r, hrf, hrl, hrq⟩ := hw.mem (by omega) ⟨hq, by omega⟩
        rw [hs, hrq]
        exact hv r hrf (by omega)
  · simpa only [hs, he] using (Frame.of_window (n := n) (starts := oldstarts)
      (ends := oldends) hw)

theorem valid (h : Complete n first last oldlab hits oldstarts oldends s)
    (hp : CountPartition level first last s.lab hits before s.ptn)
    (hc : IsCell before level first (last + 1 - first))
    (hi : Valid n oldlab before level oldstarts oldends) :
    Valid n s.lab s.ptn level s.cellstart s.cellend :=
  h.runs.valid hp hc hi h.frame.ends h.frame.starts

theorem of_two {n : Nat} {s : RefineSt n} (hm : Minima.Permuted s.lab lab s.hits first last v2 last last w1 w2 cap)
    (ht : Two n first v2 last last lab starts)
    (hf : Frame n first (last - 1) s.lab lab s.cellstart starts s.cellend s.cellend)
    (hv : v2 < last) (hb : last ≤ n) (he : s.cellend.size = n) :
    Complete n first (last - 1) s.lab s.hits s.cellstart s.cellend
      { s with
        lab := lab
        cellstart := starts
        cellend := (s.cellend.setIfInBounds first (v2 - 1)).setIfInBounds v2 (last - 1) } := by
  have bounds := hm.bounds
  have hlast : last - 1 + 1 = last := by omega
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hlast] using hm.window
  · simpa only [hlast] using ht.runs hm.toMinima hv hb he
  · exact (hf.set_end ⟨by omega, by omega⟩).set_end ⟨by omega, by omega⟩

/-- The completed second-fragment scatter establishes the return cache when
there is no larger-count tail. -/
theorem of_scatter {n : Nat} {s : RefineSt n}
    (hm : Minima.Permuted s.lab lab s.hits first last v2 last last w1 w2 cap)
    (ht : Two n first v2 last (v2 + (last - v2)) lab starts)
    (hf : Frame n first s.cellend[first]! s.lab lab s.cellstart starts s.cellend s.cellend)
    (hlast : s.cellend[first]! + 1 = last)
    (hv : v2 < last) (hb : last ≤ n) (he : s.cellend.size = n) :
    Sort.Window s.lab lab first last ∧
    Runs n first s.cellend[first]! last lab s.hits starts
      ((s.cellend.setIfInBounds first (v2 - 1)).setIfInBounds v2 (last - 1)) ∧
    Frame n first s.cellend[first]! s.lab lab s.cellstart starts s.cellend
      ((s.cellend.setIfInBounds first (v2 - 1)).setIfInBounds v2 (last - 1)) := by
  have hend : last - 1 = s.cellend[first]! := by omega
  have hh := of_two hm (by simpa only [Nat.add_sub_of_le hm.bounds.2.1] using ht)
    (by simpa only [hend] using hf) hv hb he
  simpa only [hend, hlast] using Complete.iff.mp hh

end Complete

namespace Tail

/-- Sorting the larger-count tail leaves the first two indexed runs intact
and establishes the invariant for the executed tail scan. -/
theorem initial {n : Nat} {s : RefineSt n} (hm : Minima.Permuted s.lab lab s.hits first last v2 v3 last w1 w2 cap)
    (ht : Two n first v2 v3 v3 lab starts)
    (hf : Frame n first (last - 1) s.lab lab s.cellstart starts s.cellend s.cellend)
    (hv : v2 < v3) (hb : last ≤ n) (he : s.cellend.size = n) :
    Tail n first (last - 1) (v3 - 1) s.lab s.hits s.cellstart s.cellend
      { s with
        lab := Sort.indirect lab s.hits v3 (last - v3)
        cellstart := starts
        cellend := (s.cellend.setIfInBounds first (v2 - 1)).setIfInBounds v2 (v3 - 1) } := by
  have bounds := hm.bounds
  have hlast : last - 1 + 1 = last := by omega
  have hv3 : v3 - 1 + 1 = v3 := by omega
  have hsorted := hm.toMinima.sort_tail hm.size
  have hmin := hm.toMinima.indirect hm.size
  have hwindow := hm.window.indirect (by omega : first ≤ v3)
    (by omega : v3 + (last - v3) ≤ last) hm.size (hits := s.hits)
  have htwo := ht.relabel (by omega) (Nat.le_refl _) (out := Sort.indirect lab s.hits v3 (last - v3))
    (fun q hq => Sort.indirect_outside lab s.hits v3 (last - v3) q (by have := hm.size; omega)
      (Or.inl hq))
  have hframe := (hf.set_end (a := first) (value := v2 - 1)
    ⟨by omega, by omega⟩).set_end (a := v2) (value := v3 - 1) ⟨by omega, by omega⟩
  have hsort : Sort.Window lab (Sort.indirect lab s.hits v3 (last - v3)) first (last - 1 + 1) := by
    rw [hlast]
    exact (Sort.Window.refl lab first last).indirect (by omega) (by omega) hm.size
  refine ⟨?_, ?_, ?_, ?_, rfl, by omega, ?_⟩
  · simpa only [hlast] using hwindow
  · simpa only [hlast] using hsorted
  · simpa only [hv3] using htwo.runs hmin hv hb he
  · exact hframe.relabel hsort
  · by_cases hvlast : v3 = last
    · exact Or.inl (by omega)
    · exact Or.inr (hmin.next_different hv (by omega))

end Tail

end Hex.GraphIso.Nauty.Sparse.Index
