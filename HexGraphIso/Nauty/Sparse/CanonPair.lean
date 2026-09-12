/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CanonGuide
public import HexGraphIso.Nauty.Sparse.Pairs
public import HexGraphIso.Nauty.Sparse.AncestorStab
import all HexGraphIso.Nauty.Sparse.CanonGuide
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The literal canonical scatter returned by a native child stabilizes
the frozen parent cells. Both labels are related to those cells by the
actual call's frame and canonical-reference provenance. -/
theorem child_canon_stab {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc tv : Nat} {cell : VSet n}
    {base st : State n} {key : Nat → Key n} {best : Option (Key n)}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (first childFirst : Bool) (ht : Generic.Target State.frame level tc cell st)
    (hv : cell.mem tv = true) (hbase : Ready G level numcells base)
    (hframe : FrameOut G level level base st) (hguide : CanonGuide level tc base key best st) :
    let out := (Generic.node childFirst (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    out.gcaCanon = level → out.canonlab.size = n →
      (∀ i, i < n → out.workperm[out.canonlab[i]!]! = out.lab[i]!) →
      CellStab base.ptn level base.lab out.workperm := by
  intro out he hs hmap
  obtain ⟨_, _, _, href⟩ := child_canon_locate (tcLevel := tcLevel) (fuel := fuel)
    h hn hl first childFirst ht hv hguide he
  have hc := h.child hn hl first ht hv
  have hx := node_frame G hn childFirst tcLevel fuel (level + 1) (numcells + 1)
    ((policy (n := n)).child first level tc tv st) (by omega) hc
  have hp := hframe.trans (h.child_frame hn hl first ht hv hx)
  exact hp.scatter_stab hbase hn hl hs href hmap

/-- Native automorphism soundness and the actual returned scatter justify
its explicit pair at the receiving parent's frozen partition. -/
theorem child_canon_pair {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc tv : Nat} {cell : VSet n}
    {base st : State n} {key : Nat → Key n} {best : Option (Key n)}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (first childFirst : Bool) (ht : Generic.Target State.frame level tc cell st)
    (hv : cell.mem tv = true) (hbase : Ready G level numcells base)
    (hframe : FrameOut G level level base st) (hguide : CanonGuide level tc base key best st) :
    let out := (Generic.node childFirst (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    out.gcaCanon = level → out.canonlab.size = n → Automorphism G out.workperm →
      (∀ i, i < n → out.workperm[out.canonlab[i]!]! = out.lab[i]!) →
      PairOk (Graph.context G.graph).g base.ptn base.lab level
        (fmperm out.workperm n).1 (fmperm out.workperm n).2 := by
  intro out he hs ha hmap
  apply pairOk_fmperm (labOk_of_reach hbase.ok.labSize hbase.ok.reach)
    hbase.ok.labSize hbase.ok.ptnSize (searchOk_end hn hbase.ok hl) ha.checked
  exact child_canon_stab h hn hl first childFirst ht hv hbase hframe hguide he hs hmap

end Hex.GraphIso.Nauty.Sparse
