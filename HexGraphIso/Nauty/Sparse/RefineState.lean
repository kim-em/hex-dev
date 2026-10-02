/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SingletonIndex
public import HexGraphIso.Nauty.Sparse.NontrivialIndex
public import HexGraphIso.Nauty.Sparse.SplitBounds

public section

namespace Hex.GraphIso.Nauty.Sparse.RefineSt

/-- The indexed working state has a permutation labelling, a closed bounded
partition, exact cell indices, allocated scratch, and an exact active queue. -/
structure Valid (level : Nat) (s : RefineSt n) : Prop where
  lab : s.lab.toList.Perm (List.range n)
  size : s.ptn.size = n
  closed : s.ptn[n - 1]! ≤ level
  index : Index.Valid n s.lab s.ptn level s.cellstart s.cellend
  scratch : Scratch.Bounded n s.toScratch
  queue : CellQueue s.ptn level s.active s.queue

/-- A refinement pass subdivides the original cells, retaining their vertex
multisets and charging the cell counter once for each new boundary. -/
structure Step (level : Nat) (s t : RefineSt n) : Prop where
  cuts : Cuts level n s.ptn t.ptn s.numcells t.numcells n
  cells : cellsPerm s.ptn level t.lab s.lab

namespace Step

variable {level : Nat} {s t u : RefineSt n}

theorem refl (level : Nat) (s : RefineSt n) : Step level s s :=
  ⟨Cuts.refl _ _ _ _ _, cellsPerm_refl _ _ _⟩

theorem trans (h : Step level s t) (k : Step level t u)
    (hs : Valid level s) (ht : Valid level t) (hu : Valid level u) : Step level s u :=
  ⟨h.cuts.trans k.cuts, cellsPerm_trans
    (h.cuts.perm hs.size (by simpa using ht.lab.length_eq)
      (by simpa using hu.lab.length_eq) hs.closed k.cells) h.cells⟩

end Step

namespace Valid

variable {level : Nat} {s : RefineSt n}

theorem hash (h : Valid level s) (v : Nat) : Valid level (s.hash v) :=
  ⟨h.lab, h.size, h.closed, h.index, h.scratch, h.queue⟩

theorem remove (h : Valid level s) {pos : Nat} (hp : pos < s.queue.size) :
    Valid level { s with
      active := s.active.erase s.queue[pos]!
      queue := (s.queue.setIfInBounds pos s.queue[s.queue.size - 1]!).pop } :=
  ⟨h.lab, h.size, h.closed, h.index, h.scratch, h.queue.remove hp⟩

theorem cell (h : Valid level s) {first : Nat} (hf : first < n)
    (ha : first = 0 ∨ s.ptn[first - 1]! ≤ level) :
    IsCell s.ptn level first (s.cellend[first]! + 1 - first) ∧
      first ≤ s.cellend[first]! ∧ s.cellend[first]! < n := by
  have hs := h.size
  rw [h.index.end_eq h.size h.closed hf ha]
  have hb : cellEnd s.ptn level first < n := by
    simpa only [h.size] using cellEnd_lt (ptn := s.ptn) (level := level) (i := first)
      (by omega) (by simpa only [h.size] using h.closed)
  exact ⟨isCell_cellEnd (by omega) ha (by simpa only [h.size] using h.closed), cellEnd_ge, hb⟩

theorem queue_cell (h : Valid level s) {pos : Nat} (hp : pos < s.queue.size) :
    s.queue[pos]! < n ∧
      IsCell s.ptn level s.queue[pos]! (s.cellend[s.queue[pos]!]! + 1 - s.queue[pos]!) ∧
      s.queue[pos]! ≤ s.cellend[s.queue[pos]!]! ∧ s.cellend[s.queue[pos]!]! < n := by
  have hm : s.queue[pos]! ∈ s.queue.toList := by
    rw [getElem!_pos s.queue pos hp]
    exact List.mem_iff_getElem.mpr ⟨pos, by simpa using hp, by simp⟩
  have hv := h.queue.set.bound hm
  exact ⟨hv, h.cell hv (h.queue.starts _ ((h.queue.set.mem _).mp hm))⟩

theorem counts (h : Valid level s) (first : Nat) (distance : Bool)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hb : s.cellend[first]! < n)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2) :
    Valid level (splitCounts level first distance s) ∧ Step level s (splitCounts level first distance s) := by
  have hf : first ≤ s.cellend[first]! := by have := hc.1; omega
  have hl : s.lab.size = n := by simpa using h.lab.length_eq
  have hc' := splitCounts_cuts level first distance s hl h.size hb hc hk
  refine ⟨⟨(splitCounts_perm level first distance s hf (by omega)).trans h.lab,
    (splitCounts_frame level first distance s).ptn_size.trans h.size,
    by rw [hc'.closed _ h.closed]; exact h.closed,
    splitCounts_index level first (s.cellend[first]! + 1 - first) distance s h.lab h.size
      h.index hc (by omega) (fun q hq hu => hk q hq (by omega)),
    splitCounts_bounded level first distance s h.scratch,
    splitCounts_queue level first distance s hl h.size hb hc hk h.queue⟩,
    hc', splitCounts_cells level first distance s hf (by omega) hc⟩

theorem singleton (h : Valid level s) (G : Hex.SparseGraph n) (split : Nat) (hb : split < n) :
    Valid level (splitSingleton (.ofGraph G) level split s) ∧
      Step level s (splitSingleton (.ofGraph G) level split s) := by
  have hc := splitSingleton_state G level split s h.lab h.size h.closed hb h.index
    ⟨h.scratch.marks_size, h.scratch.marks_le⟩ ⟨h.scratch.vmarks_size, h.scratch.vmarks_le⟩
  exact ⟨⟨hc.1, hc.2.1, by rw [hc.2.2.2.1.closed _ h.closed]; exact h.closed,
    hc.2.2.1, splitSingleton_bounded _ _ _ _ h.scratch, hc.2.2.2.2.1 h.queue⟩,
    hc.2.2.2.1, hc.2.2.2.2.2.1⟩

theorem nontrivial (h : Valid level s) (G : Hex.SparseGraph n) (split len : Nat)
    (hc : IsCell s.ptn level split len) (hb : split + len ≤ n) :
    Valid level (splitNontrivial (.ofGraph G) level split s) ∧
      Step level s (splitNontrivial (.ofGraph G) level split s) := by
  have ht := splitNontrivial_state G level split len s h.lab h.size h.closed h.index hc hb
    ⟨h.scratch.marks_size, h.scratch.marks_le⟩ h.scratch.hits_size
  exact ⟨⟨ht.1, ht.2.1, by rw [ht.2.2.2.1.closed _ h.closed]; exact h.closed,
    ht.2.2.1, splitNontrivial_bounded _ _ _ _ h.scratch, ht.2.2.2.2.2.1 h.queue⟩,
    ht.2.2.2.1, ht.2.2.2.2.1⟩

end Valid
end Hex.GraphIso.Nauty.Sparse.RefineSt
