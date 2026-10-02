/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexFrame
public import HexGraphIso.Nauty.Sparse.IndexTwo
public import HexGraphIso.Nauty.Sparse.Refine

public section

namespace Hex.GraphIso.Nauty.Sparse

theorem Sort.Sorted.le (h : Sort.Sorted lab hits first len)
    (hi : first ≤ i) (hij : i ≤ j) (hj : j < first + len) :
    hits[lab[i]!]! ≤ hits[lab[j]!]! := by
  by_cases he : i = j
  · subst j
    exact Nat.le_refl _
  · have hx := h (i - first) (j - first) (by omega) (by omega)
    simpa only [show first + (i - first) = i by omega,
      show first + (j - first) = j by omega] using hx

namespace Index

/-- Completed count runs through `upto`, with the next count change located.
The partition boundary at `upto` may still await the next outer iteration. -/
structure Tail (n first last upto : Nat) (oldlab hits oldstarts oldends : Array Nat)
    (s : RefineSt n) : Prop where
  window : Sort.Window oldlab s.lab first (last + 1)
  sorted : Sort.Sorted s.lab hits first (last + 1 - first)
  runs : Runs n first last (upto + 1) s.lab hits s.cellstart s.cellend
  frame : Frame n first last oldlab s.lab oldstarts s.cellstart oldends s.cellend
  hits_eq : s.hits = hits
  bounds : first ≤ upto ∧ upto ≤ last
  next : upto = last ∨ hits[s.lab[upto]!]! ≠ hits[s.lab[upto + 1]!]!

namespace Tail

theorem transfer (h : Tail n first last upto oldlab hits oldstarts oldends s)
    (hl : t.lab = s.lab) (hs : t.cellstart = s.cellstart)
    (he : t.cellend = s.cellend) (hh : t.hits = s.hits) :
    Tail n first last upto oldlab hits oldstarts oldends t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, h.bounds, ?_⟩
  · simpa only [hl] using h.window
  · simpa only [hl] using h.sorted
  · simpa only [hl, hs, he] using h.runs
  · simpa only [hl, hs, he] using h.frame
  · exact hh.trans h.hits_eq
  · simpa only [hl] using h.next

/-- Sorted counts and equal endpoint values identify every vertex of the
run found by the inner scan. -/
theorem run (h : Tail n first last upto oldlab hits oldstarts oldends s)
    (hu : upto < last) (ha : upto + 1 ≤ b) (hb : b ≤ last)
    (hk : hits[s.lab[b]!]! = hits[s.lab[upto + 1]!]!)
    (hn : b = last ∨ hits[s.lab[b]!]! ≠ hits[s.lab[b + 1]!]!) :
    Run s.lab hits first last (upto + 1) b := by
  have bounds := h.bounds
  refine ⟨by omega, Or.inr ?_, ?_, hn⟩
  · simp only [Nat.add_sub_cancel]
    exact h.next.resolve_left (by omega)
  · intro q hq hq'
    have hlo := h.sorted.le (i := upto + 1) (j := q) (by omega) hq (by omega)
    have hhi := h.sorted.le (i := q) (j := b) (by omega) hq' (by omega)
    rw [hk] at hhi
    exact Nat.le_antisymm hhi hlo

/-- Completing the inner scatter and writing its first vertex and endpoint
extends the cache by exactly the discovered run. -/
theorem extend (h : Tail n first last upto oldlab hits oldstarts oldends s)
    (hp : oldlab.toList.Perm (List.range n)) (hu : upto < last) (hbn : last < n)
    (ha : upto + 1 ≤ b) (hb : b ≤ last)
    (hk : hits[s.lab[b]!]! = hits[s.lab[upto + 1]!]!)
    (hn : b = last ∨ hits[s.lab[b]!]! ≠ hits[s.lab[b + 1]!]!)
    (hs : Scatter n s.lab s.cellstart starts (upto + 1 + 1) (b + 1) (upto + 1)) :
    Tail n first last b oldlab hits oldstarts oldends
      { s with
        cellstart := starts.setIfInBounds s.lab[upto + 1]! (if upto + 1 = b then n else upto + 1)
        cellend := s.cellend.setIfInBounds (upto + 1) b } := by
  have bounds := h.bounds
  have perm := h.window.perm.trans hp
  have scatter := hs.prepend (fun i hi => perm_bound perm hi)
    (fun i j hi hj he => perm_injective perm hi hj he) ha (by omega)
  have hr := h.run hu ha hb hk hn
  refine ⟨h.window, h.sorted, ?_, ?_, h.hits_eq, by omega, hn⟩
  · apply h.runs.extend hr (by omega) scatter.size
    intro q hq
    rw [scatter.get q hq]
    simp only [Nat.lt_add_one_iff]
  · exact (h.frame.scatter scatter (by omega) (by omega)).set_end ⟨by omega, by omega⟩

end Tail

end Index

end Hex.GraphIso.Nauty.Sparse
