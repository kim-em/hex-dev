/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountCongr

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Permuting vertices within input cells does not change the ordered
count classes produced by the optimized count splitter. -/
theorem splitCounts_invariant (level first last : Nat) (distance : Bool) (s t : RefineSt n)
    (hsl : s.lab.toList.Perm (List.range n)) (htl : t.lab.toList.Perm (List.range n))
    (hsp : s.ptn.size = n) (htp : t.ptn = s.ptn) (hh : t.hits = s.hits)
    (hse : s.cellend[first]! = last) (hte : t.cellend[first]! = last)
    (hf : first ≤ last) (hb : last < n)
    (hsk : ∀ q, first ≤ q → q ≤ last → s.hits[s.lab[q]!]! < n + 2)
    (htk : ∀ q, first ≤ q → q ≤ last → t.hits[t.lab[q]!]! < n + 2)
    (hc : IsCell s.ptn level first (last + 1 - first))
    (hp : cellsPerm s.ptn level s.lab t.lab) :
    (splitCounts level first distance s).ptn = (splitCounts level first distance t).ptn ∧
      cellsPerm (splitCounts level first distance s).ptn level
        (splitCounts level first distance s).lab (splitCounts level first distance t).lab := by
  have hs : s.lab.size = n := by simpa using hsl.length_eq
  have ht : t.lab.size = n := by simpa using htl.length_eq
  have hkeys : ((segN s.lab first (last + 1 - first)).map fun v => s.hits[v]!).Perm
      ((segN t.lab first (last + 1 - first)).map fun v => t.hits[v]!) := by
    rw [hh]
    exact (hp _ _ hc).map _
  have heq := splitCounts_ptn level first last distance s t hs ht hsp htp hse hte hf hb hsk htk hkeys
  refine ⟨heq, ?_⟩
  intro a len ha
  have hpart := splitCounts_partition level first distance s hs hsp (by omega) (by omega)
    (fun q hq he => hsk q hq (by omega))
  rw [hse] at hpart
  rcases hpart.nesting hc ha with hleft | hright | ⟨hfirst, hlast⟩
  · have hc' := hpart.cell_outside ha (Or.inl hleft)
    have hs' : segN (splitCounts level first distance s).lab a len = segN s.lab a len :=
      segN_congr fun i hi => splitCounts_outside level first distance s
        (by omega) (by omega) (a + i) (by omega)
    have ht' : segN (splitCounts level first distance t).lab a len = segN t.lab a len :=
      segN_congr fun i hi => splitCounts_outside level first distance t
        (by omega) (by omega) (a + i) (by omega)
    rw [hs', ht']
    exact hp a len hc'
  · have hc' := hpart.cell_outside ha (Or.inr hright)
    have hs' : segN (splitCounts level first distance s).lab a len = segN s.lab a len :=
      segN_congr fun i hi => splitCounts_outside level first distance s
        (by omega) (by omega) (a + i) (by omega)
    have ht' : segN (splitCounts level first distance t).lab a len = segN t.lab a len :=
      segN_congr fun i hi => splitCounts_outside level first distance t
        (by omega) (by omega) (a + i) (by omega)
    rw [hs', ht']
    exact hp a len hc'
  · have hs' := splitCounts_class level first distance s hsl hsp (by omega) (by omega)
      (fun q hq he => hsk q hq (by omega)) (by simpa only [hse] using hc)
      hfirst ha.1 (by omega) ha
    have ht' := splitCounts_class level first distance t htl (by rw [htp]; exact hsp)
      (by omega) (by omega) (fun q hq he => htk q hq (by omega))
      (by simpa only [hte, htp] using hc) hfirst ha.1 (by omega) (by rw [← heq]; exact ha)
    have hk := splitCounts_keys level first last distance s t hs ht hse hte hf hb
      (hsk first (by omega) hf) (htk first (by omega) hf) hkeys hfirst (by have := ha.1; omega)
    rw [hh] at hk
    rw [hse, hk] at hs'
    rw [hte, hh] at ht'
    exact hs'.trans (((hp _ _ hc).filter _).trans ht'.symm)

end Hex.GraphIso.Nauty.Sparse
