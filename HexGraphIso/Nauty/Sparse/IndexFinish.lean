/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexRuns

public section

namespace Hex.GraphIso.Nauty.Sparse.Index

/-- Completed run entries and preservation outside the split establish full
cache validity for the new partition. -/
theorem Runs.valid (h : Runs n first last (last + 1) lab hits starts ends)
    (hp : CountPartition level first last lab hits before ptn)
    (hc : IsCell before level first (last + 1 - first))
    (hi : Valid n oldlab before level oldstarts oldends)
    (he : ∀ q, q < first ∨ last < q → ends[q]! = oldends[q]!)
    (hs : ∀ q, q < n → q < first ∨ last < q → starts[lab[q]!]! = oldstarts[oldlab[q]!]!) :
    Valid n lab ptn level starts ends := by
  refine ⟨h.starts_size, h.ends_size, ?_, ?_⟩
  · intro a len ha hb han
    have hlen := ha.1
    rcases hp.nesting hc ha with hd | hd | ⟨hal, hbl⟩
    · rw [he a (Or.inl (by omega))]
      exact hi.ends_eq a len (hp.cell_outside ha (Or.inl hd)) hb han
    · rw [he a (Or.inr hd)]
      exact hi.ends_eq a len (hp.cell_outside ha (Or.inr hd)) hb han
    · have hr : Run lab hits first last a (a + len - 1) := by
        apply (Run.cell hp hc hal (by omega) (by omega)).mp
        simpa only [show a + len - 1 + 1 - a = len by omega] using ha
      exact h.ends_eq a _ hr (by omega)
  · intro a len ha hb han q hq hq'
    have hlen := ha.1
    rcases hp.nesting hc ha with hd | hd | ⟨hal, hbl⟩
    · rw [hs q (by omega) (Or.inl (by omega))]
      exact hi.starts_eq a len (hp.cell_outside ha (Or.inl hd)) hb han q hq hq'
    · rw [hs q (by omega) (Or.inr (by omega))]
      exact hi.starts_eq a len (hp.cell_outside ha (Or.inr hd)) hb han q hq hq'
    · have hr : Run lab hits first last a (a + len - 1) := by
        apply (Run.cell hp hc hal (by omega) (by omega)).mp
        simpa only [show a + len - 1 + 1 - a = len by omega] using ha
      rw [h.starts_eq a _ hr (by omega) q hq (by omega)]
      have heq : a = a + len - 1 ↔ len = 1 := by omega
      simp only [heq]

end Hex.GraphIso.Nauty.Sparse.Index
