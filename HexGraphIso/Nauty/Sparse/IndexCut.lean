/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexBinary

public section

namespace Hex.GraphIso.Nauty.Sparse.Index

/-- A binary split installs a complete valid cache after its literal partition
and endpoint writes. All other cells keep their old cache entries. -/
theorem Two.valid {n level first cut last : Nat}
    {lab oldlab ptn oldstarts starts oldends : Array Nat}
    (h : Two n first cut last last lab starts)
    (hi : Valid n oldlab ptn level oldstarts oldends)
    (hc : IsCell ptn level first (last - first)) (hs : ptn.size = n)
    (hf : first < cut) (hl : cut < last) (hb : last ≤ n)
    (hframe : Frame n first (last - 1) oldlab lab oldstarts starts oldends oldends) :
    Valid n lab (ptn.setIfInBounds (cut - 1) level) level starts
      ((oldends.setIfInBounds first (cut - 1)).setIfInBounds cut (last - 1)) := by
  have hcut : cut - 1 < ptn.size := by rw [hs]; omega
  have hout := (hframe.set_end (a := first) (value := cut - 1)
    ⟨by omega, by omega⟩).set_end (a := cut) (value := last - 1) ⟨by omega, by omega⟩
  refine ⟨h.size, by simpa using hi.ends_size, ?_, ?_⟩
  · intro a len ha han hab
    have hpos := ha.1
    rcases CellCut.cells hc hf hl hcut ha with ⟨ho, haold⟩ | ⟨haeq, hlen⟩ | ⟨haeq, hlen⟩
    · rw [hout.ends a (by omega)]
      exact hi.ends_eq a len haold han hab
    · subst a len
      change ((oldends.set! first (cut - 1)).set! cut (last - 1))[first]! = first + (cut - first) - 1
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
        Array.getElem!_set!_self _ _ _ (by rw [hi.ends_size]; omega)]
      omega
    · subst a len
      change ((oldends.set! first (cut - 1)).set! cut (last - 1))[cut]! = cut + (last - cut) - 1
      rw [Array.getElem!_set!_self _ _ _ (by simp only [Array.size_set!]; rw [hi.ends_size]; omega)]
      omega
  · intro a len ha han hab q hq hu
    have hpos := ha.1
    rcases CellCut.cells hc hf hl hcut ha with ⟨ho, haold⟩ | ⟨haeq, hlen⟩ | ⟨haeq, hlen⟩
    · rw [hout.starts q (by omega) (by omega)]
      exact hi.starts_eq a len haold han hab q hq hu
    · subst a len
      rw [h.minimum q hq (by omega)]
      have heq : (cut = first + 1) ↔ (cut - first = 1) := by omega
      simp only [heq]
    · subst a len
      rw [h.second q hq (by omega)]
      have heq : (last = cut + 1) ↔ (last - cut = 1) := by omega
      simp only [heq]

end Hex.GraphIso.Nauty.Sparse.Index
