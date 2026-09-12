/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountSize
public import HexGraphIso.Nauty.Sparse.Boundary
public import HexGraphIso.Nauty.Invariant.Reach

public section

namespace Hex.GraphIso.Nauty

/-- Recovery identifies two bounded partition arrays when their values agree
at every boundary visible at the receiving level. Storage is arbitrary. -/
theorem recover_ptn_congr (inf level : Nat) (s t : SearchState n κ)
    (hs : s.ptn.size = n) (ht : t.ptn.size = n)
    (hlow : ∀ q : Nat, s.ptn[q]! ≤ level ∨ t.ptn[q]! ≤ level → t.ptn[q]! = s.ptn[q]!) :
    (recover inf level t).ptn = (recover inf level s).ptn := by
  apply Array.ext
  · rw [recover_ptn_size, recover_ptn_size, hs, ht]
  · intro q hq hq'
    have hqn : q < n := by simpa only [recover_ptn_size, ht] using hq
    rw [← getElem!_pos _ q hq, ← getElem!_pos _ q hq', recover_ptn, recover_ptn]
    by_cases he : s.ptn[q]! ≤ level
    · have hv := hlow q (Or.inl he)
      rw [hv]
    · have hafter : level < t.ptn[q]! := by
        by_cases hc : t.ptn[q]! ≤ level
        · have hv := hlow q (Or.inr hc)
          omega
        · omega
      simp only [hqn, hafter, show level < s.ptn[q]! by omega, and_self, ite_true]

namespace Sparse

/-- Count splitting retains every boundary visible to an ancestor, from
either side of the refinement. -/
theorem splitCounts_low (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hb : s.cellend[first]! < n)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (parent : Nat) (hp : parent < level) (q : Nat)
    (hq : s.ptn[q]! ≤ parent ∨ (splitCounts level first distance s).ptn[q]! ≤ parent) :
    (splitCounts level first distance s).ptn[q]! = s.ptn[q]! := by
  rcases hq with hq | hq
  · exact splitCounts_closed level first distance s hl hs hb hc hk q (by omega)
  · rcases (splitCounts_boundary level first distance s).values q with he | he
    · exact he
    · omega

/-- The actual recovery operation erases this descendant count split while
retaining its ancestor partition. This applies to the sparse canonical store
as well as to every other shared search-storage type. -/
theorem splitCounts_recover (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hb : s.cellend[first]! < n)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (inf parent : Nat) (hp : parent < level) (st : SearchState n κ) :
    (Nauty.recover inf parent { st with ptn := (splitCounts level first distance s).ptn }).ptn =
      (Nauty.recover inf parent { st with ptn := s.ptn }).ptn := by
  apply recover_ptn_congr
  · exact hs
  · exact (splitCounts_cuts level first distance s hl hs hb hc hk).size.trans hs
  · intro q hq
    exact splitCounts_low level first distance s hl hs hb hc hk parent hp q hq

end Sparse
end Hex.GraphIso.Nauty
