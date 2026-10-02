/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ResumeCover
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.CursorCover
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Receiving an actual off-path child composes its maximum result with
both native filters, parent recovery and the next executable cursor. The
workspace validity and frame of the resumed state come from the complete
native child call, rather than additional continuation assumptions. -/
theorem Cell.Cover.advance {G : GraphIso.Sparse.Colored n k} {tcLevel runFuel : Nat}
    {c : Cell n} {st out : State n} {cell : VSet n} {tv tv1 index : Nat} {bs : List Nat}
    {first short : Bool} {witness : Nat → Option (Key n) → Prop}
    {next : Generic.SweepFn (State n) n} {result : Exit × Nat × State n → Prop}
    (h : c.Cover G.graph tcLevel (Remaining (some tv) cell) (State.key G.graph bs st))
    (hc : c.Valid G) (he : FrameOut G c.level c.level c.entry st)
    (hp : PairsReady G tcLevel c.level c.numcells st)
    (ht : Generic.Target State.frame c.level c.tc cell st) (hv : cell.mem tv = true)
    (hs : ∀ v, cell.mem v = true → c.vertices.mem v = true)
    (hrecord : CheapRecorded c.level c.tc st) (hcanon : st.gcaCanon ≤ c.level) (hcap : 0 < st.wsCap)
    (hguide : CanonGuide c.level c.tc c.entry (c.key G.graph tcLevel) (State.key G.graph bs st) st)
    (hcall : Generic.node false (.ofGraph G.graph) (n + 2) tcLevel runFuel
      (c.level + 1) (c.numcells + 1) ((policy (n := n)).child first c.level c.tc tv st) =
        (.unwind c.level short, out))
    (hr : MaxResult ((c.child first st tv).key G.graph tcLevel)
      (State.key G.graph bs (c.child first st tv).entry) (State.best G.graph out)
      c.level witness (.unwind c.level short))
    (hnext : let back := (policy (n := n)).recover (n + 2) c.level ((policy (n := n)).leaveChild tv out)
      ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) → ∀ index,
        FrameOut G c.level c.level c.entry back → PairsReady G tcLevel c.level c.numcells back →
        c.Cover G.graph tcLevel (Remaining (smaller.nextElem (some tv)) smaller) (State.best G.graph back) →
        result (next first c.level c.numcells c.tc tv1 (smaller.nextElem (some tv)) smaller index back)) :
    result (Generic.advance (n + 2) next first c.level c.numcells c.tc tv1 tv cell index
      ((policy (n := n)).leaveChild tv out) (.unwind c.level short)) := by
  let left := (policy (n := n)).leaveChild tv out
  let back := (policy (n := n)).recover (n + 2) c.level left
  have hn : 0 < n := by have := hc.positive; have := hc.depth; omega
  have hch := hp.child hn hc.positive first ht hv hrecord
  have hpairs := node_pairs G hn tcLevel runFuel (c.level + 1) (c.numcells + 1)
    ((policy (n := n)).child first c.level c.tc tv st) (by omega) hch
  have hpairs' : PairsReady G tcLevel c.level c.numcells back := by
    have hh := hp.child_return hn hc.positive first runFuel ht hv hrecord hpairs
    rw [hcall] at hh
    exact hh.1
  have hframe := node_frame G hn false tcLevel runFuel (c.level + 1) (c.numcells + 1)
    ((policy (n := n)).child first c.level c.tc tv st) (by omega) hch.node
  rw [hcall] at hframe
  have hparent := hp.ready.child_frame hn hc.positive first ht hv
    (by simpa only [Nat.add_sub_cancel] using hframe)
  have hback : FrameOut G c.level c.level c.entry back :=
    he.trans (hp.ready.recover hn hc.positive (hparent.leave tv)).2
  have hvisit : c.Cover G.graph tcLevel (Remaining (cell.nextElem (some tv)) cell) (State.best G.graph left) :=
    h.received hc he hp.ready (hs tv hv) hr
  have hresume : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      c.Cover G.graph tcLevel (Remaining (smaller.nextElem (some tv)) smaller) (State.best G.graph left) →
      result (Generic.resume (n + 2) next first c.level c.numcells c.tc tv1 tv smaller index left) := by
    intro smaller hsub hcover
    apply hcover.resume hc hback hpairs' (fun v hv => hs v (hsub v hv))
    intro filtered hfiltered index hfilteredCover
    exact hnext filtered (fun v hv => hsub v (hfiltered v hv)) index hback hpairs' hfilteredCover
  unfold Generic.advance
  simp only [Nat.lt_irrefl, ite_false, Id.run_pure, apply_ite Id.run]
  cases short with
  | false => exact hresume cell (fun _ hv => hv) hvisit
  | true =>
    have hshort := hvisit.short hc he hp ht hv hrecord hcanon hcap
      (congrArg Prod.fst hcall) (Nat.le_refl _) hguide
      (fun v hv => hs v hv.1) (fun _ hv => hv.1)
    rw [hcall] at hshort
    have hsub : ∀ v, ((policy (n := n)).shortprune cell left).mem v = true → cell.mem v = true :=
      fun _ hv => Nauty.shortprune_subset (st := left.frame) hv
    exact hresume _ hsub (hshort.filtered hsub)

end Hex.GraphIso.Nauty.Sparse.Max
