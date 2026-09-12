/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountActive
public import HexGraphIso.Nauty.Sparse.CountPattern

public section

namespace Hex.GraphIso.Nauty.Sparse.Activation

/-- A complete native count split composes the per-cell activation rule
through the touched-cell fold and the distance-cell fold. -/
theorem counts {before : Array Nat} {active : VSet n}
    (level first : Nat) (distance : Bool) (s : RefineSt n)
    (h : Activation n level before s.ptn active s.active)
    (hc : IsCell before level first (s.cellend[first]! + 1 - first))
    (ht : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hb : s.cellend[first]! < n)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2) :
    let t := splitCounts level first distance s
    Activation n level before t.ptn active t.active := by
  have ha := splitCounts_active level first distance s hl hb ht hk
  have hp := splitCounts_partition level first distance s hl hs (by have := ht.1; omega) hb hk
  apply h.step hc ha.1 ha.2
  intro q hq
  rcases hq with hq | hq
  · exact hp.head q hq
  · exact hp.tail q (by omega)

end Hex.GraphIso.Nauty.Sparse.Activation
