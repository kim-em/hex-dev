/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FillIndex
public import HexGraphIso.Nauty.Sparse.IndexCut
public import HexGraphIso.Nauty.Sparse.IndexReindex

public section

namespace Hex.GraphIso.Nauty.Sparse.Compact

/-- Compaction, reverse reinsertion, and the singleton splitter's conditional
boundary and sentinel writes preserve the complete cell cache. Uniform cells
retain their partition; a mixed cell receives exactly the two new endpoints. -/
theorem cache {n level first last cut : Nat}
    {before lab hit out ptn oldstarts starts ends : Array Nat} {p : Nat → Bool} {seen : List Nat}
    (h : Compact before p first last seen lab hit cut)
    (hs : seen = (before.toList.drop first).take (last - first))
    (hr : Fill lab hit.toList.reverse cut hit.toList.reverse.length out)
    (hw : Index.Writes n oldstarts starts hit.toList.reverse cut)
    (hp : before.toList.Perm (List.range n)) (hptn : ptn.size = n)
    (hi : Index.Valid n before ptn level oldstarts ends)
    (hc : IsCell ptn level first (last - first)) (hn : first + 1 < last) :
    let changed := cut ≠ last ∧ cut ≠ first
    let middle := if cut = first + 1 then starts.setIfInBounds out[first]! n else starts
    Index.Valid n out (if changed then ptn.setIfInBounds (cut - 1) level else ptn) level
      (if changed then (if last = cut + 1 then middle.setIfInBounds out[cut]! n else middle) else starts)
      (if changed then (ends.setIfInBounds first (cut - 1)).setIfInBounds cut (last - 1) else ends) := by
  have bounds := h.bounds
  have hsize : before.size = n := by simpa using hp.length_eq
  have hb : last ≤ n := by omega
  have hseen : seen.length = last - first := by
    rw [hs]
    simp only [List.length_take, List.length_drop, Array.length_toList]
    omega
  have hextent := h.extent hseen
  have hwindow := h.restore hs hr
  have hout := hwindow.perm.trans hp
  have hscatter := hr.scatter hout hw
  simp only [List.length_reverse, Array.length_toList, hextent] at hscatter
  have huniform (q : Nat) (hq : first ≤ q) (hu : q < last) : oldstarts[out[q]!]! = first := by
    obtain ⟨r, hrf, hrl, hread⟩ := hwindow.mem (by have := hwindow.size; omega) ⟨hq, hu⟩
    rw [hread, hi.starts_eq first (last - first) hc (by omega) (by omega) r hrf (by omega),
      ite_eq_right (by omega)]
  have hlast : last - 1 + 1 = last := by omega
  have hframe : Index.Frame n first (last - 1) before out oldstarts oldstarts ends ends := by
    apply Index.Frame.of_window
    simpa only [hlast] using hwindow
  have hframe' := hframe.scatter hscatter (by omega) (by omega)
  dsimp only
  by_cases hd : cut ≠ last ∧ cut ≠ first
  · simp only [ite_eq_left hd]
    have htwo := Index.Two.of_scatter hscatter hout (by omega) (by omega) hb
      (fun q hq hu => huniform q hq (by omega))
    exact htwo.valid hi hc hptn (by omega) (by omega) hb
      (hframe'.sentinels hout (by omega) (by omega) hb)
  · simp only [ite_eq_right hd]
    apply hi.reindex hc hw.size hframe'
    intro q hq hu
    rw [hscatter.get q (by omega), ite_eq_right (show last ≠ first + 1 by omega)]
    by_cases he : cut = first
    · rw [he, ite_eq_left ⟨hq, hu⟩]
    · have he' : cut = last := by omega
      rw [ite_eq_right (by omega)]
      exact huniform q hq hu

end Hex.GraphIso.Nauty.Sparse.Compact
