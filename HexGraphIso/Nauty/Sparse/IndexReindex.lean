/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexFrame

public section

namespace Hex.GraphIso.Nauty.Sparse.Index

/-- With the partition unchanged, correct indices on one cell and retained
exterior entries suffice for complete cache validity. -/
theorem Valid.reindex {n level first last : Nat}
    {oldlab lab ptn oldstarts starts ends : Array Nat}
    (h : Valid n oldlab ptn level oldstarts ends)
    (hc : IsCell ptn level first (last - first)) (hs : starts.size = n)
    (hf : Frame n first (last - 1) oldlab lab oldstarts starts ends ends)
    (hg : ∀ q, first ≤ q → q < last →
      starts[lab[q]!]! = if last = first + 1 then n else first) :
    Valid n lab ptn level starts ends := by
  have hpos := hc.1
  refine ⟨hs, h.ends_size, h.ends_eq, ?_⟩
  intro a len ha hb han q hq hu
  have hlen := ha.1
  rcases isCell_disjoint_or_eq hc ha with ho | ho | ⟨haeq, hleq⟩
  · rw [hf.starts q (by omega) (Or.inl (by omega))]
    exact h.starts_eq a len ha hb han q hq hu
  · rw [hf.starts q (by omega) (Or.inr (by omega))]
    exact h.starts_eq a len ha hb han q hq hu
  · have he : a = first := haeq.symm
    have he' : len = last - first := hleq.symm
    subst a len
    rw [hg q hq (by omega)]
    have hh : (last = first + 1) ↔ (last - first = 1) := by omega
    simp only [hh]

end Hex.GraphIso.Nauty.Sparse.Index
