/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FilterCover
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A short filter needs local validity of its newest pair. The pair may
come from a returned child's unrecovered state while coverage stays in
the parent's partition and labelling. -/
theorem filter_pair {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc len : Nat}
    {cell : VSet n} {st filter : Search n} {cs : List Nat}
    {live : Nat → Prop} {best : Option (Key n)}
    (h : SearchOk G level numcells st)
    (hn0 : 0 < n) (hlevel : 1 ≤ level) (hgsz : ctx.g.size = n)
    (hc : IsCell st.ptn level tc len) (hr : tc + len ≤ n)
    (hfuel : level + 1 + fuel ≤ n + 1)
    (hcover : CellCover ctx tcLevel fuel level numcells tc len cs st live best)
    (hsub : ∀ v, live v → (windowSet n st.lab tc len).mem v = true)
    (hmem : ∀ v, live v → cell.mem v = true)
    (hlast : ∀ fix mcr, filter.autos.back? = some (fix, mcr) →
      PairOk ctx.g st.ptn st.lab level fix mcr) :
    CellCover ctx tcLevel fuel level numcells tc len cs st
      (fun v => live v ∧ (shortprune cell filter).mem v = true) best := by
  apply ChildCover.pruned hcover (labOk_of_reach h.labSize h.reach)
    hc (by change tc + len ≤ st.lab.size; rw [h.labSize]; exact hr) hsub
  · intro γ ha hs v hv
    exact congrArg (prefixKey cs)
      (h.vertex_key hn0 hlevel hgsz ha hs hc hr hv hfuel tcLevel)
  · intro v hv hd
    exact Nauty.shortprune_drop (st := filter) (windowSet_lt (hsub v hv)) (hmem v hv) hd hlast

end Hex.GraphIso.Nauty
