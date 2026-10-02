/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SortedKeys

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- In a sorted cell, one maximal run contains every occurrence of its key. -/
theorem Index.Run.key_iff (h : Index.Run lab hits first last a b)
    (hs : Sort.Sorted lab hits first (last + 1 - first))
    (hq : first ≤ q) (he : q ≤ last) :
    hits[lab[q]!]! = hits[lab[a]!]! ↔ a ≤ q ∧ q ≤ b := by
  have bounds := h.bounds
  constructor
  · intro hk
    constructor
    · by_cases ha : a ≤ q
      · exact ha
      · have hl := hs.le (i := q) (j := a - 1) hq (by omega) (by omega)
        have hr := hs.le (i := a - 1) (j := a) (by omega) (by omega) (by omega)
        rcases h.left with hh | hh
        · omega
        · exact False.elim (hh (Nat.le_antisymm hr (by simpa only [hk] using hl)))
    · by_cases hb : q ≤ b
      · exact hb
      · have hl := hs.le (i := b) (j := b + 1) (by omega) (by omega) (by omega)
        have hr := hs.le (i := b + 1) (j := q) (by omega) (by omega) (by omega)
        have hb' := h.equal b (by omega) (by omega)
        rcases h.right with hh | hh
        · omega
        · exact False.elim (hh (Nat.le_antisymm hl (by simpa only [hk, hb'] using hr)))
  · rintro ⟨ha, hb⟩
    exact h.equal q ha hb

/-- The vertices of a completed count run are exactly the original cell
filtered by that count. Their internal order is immaterial. -/
theorem Index.Run.filter_perm (h : Index.Run lab hits first last a b)
    (hs : Sort.Sorted lab hits first (last + 1 - first))
    (hp : lab.toList.Perm (List.range n)) (hb : last < n) :
    (segN lab a (b + 1 - a)).Perm
      ((segN lab first (last + 1 - first)).filter fun v => hits[v]! == hits[lab[a]!]!) := by
  have bounds := h.bounds
  apply (List.perm_ext_iff_of_nodup (segN_nodup hp (by omega))
    ((segN_nodup hp (by omega)).filter _)).mpr
  intro v
  constructor
  · intro hv
    obtain ⟨i, hi, he⟩ := mem_segN_iff.mp hv
    apply List.mem_filter.mpr
    refine ⟨mem_segN_iff.mpr ⟨a + i - first, by omega, ?_⟩, ?_⟩
    · simpa only [show first + (a + i - first) = a + i by omega] using he
    · apply beq_iff_eq.mpr
      rw [← he]
      exact h.equal (a + i) (by omega) (by omega)
  · intro hv
    obtain ⟨hm, hk⟩ := List.mem_filter.mp hv
    obtain ⟨i, hi, he⟩ := mem_segN_iff.mp hm
    have hkey : hits[lab[first + i]!]! = hits[lab[a]!]! := by
      rw [he]
      exact beq_iff_eq.mp hk
    have hq := (h.key_iff hs (q := first + i) (by omega) (by omega)).mp hkey
    apply mem_segN_iff.mpr
    refine ⟨first + i - a, by omega, ?_⟩
    simpa only [show a + (first + i - a) = first + i by omega] using he

/-- The executed count splitter's ordered fragments have exactly their
specified count-class vertex multisets. -/
theorem splitCounts_class (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < n)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (ha : first ≤ a) (hlen : 0 < len) (he : a + len ≤ s.cellend[first]! + 1)
    (ho : IsCell (splitCounts level first distance s).ptn level a len) :
    (segN (splitCounts level first distance s).lab a len).Perm
      ((segN s.lab first (s.cellend[first]! + 1 - first)).filter
        fun v => s.hits[v]! == s.hits[(splitCounts level first distance s).lab[a]!]!) := by
  have hl : s.lab.size = n := by simpa using hp.length_eq
  have hpart := splitCounts_partition level first distance s hl hs hf hb hk
  have hrun := (Index.Run.cell hpart hc ha (by omega : a ≤ a + len - 1) (by omega)).mp
    (by simpa only [show a + len - 1 + 1 - a = len by omega] using ho)
  have hord := splitCounts_sorted level first distance s hf (by omega) (hk first (by omega) hf)
  have hout := (splitCounts_perm level first distance s hf (by omega)).trans hp
  have hfilter := hrun.filter_perm hord hout hb
  have hseg := (splitCounts_cells level first distance s hf (by omega) hc) _ _ hc
  simp only [show a + len - 1 + 1 - a = len by omega] at hfilter
  exact hfilter.trans (hseg.filter _)

end Hex.GraphIso.Nauty.Sparse
