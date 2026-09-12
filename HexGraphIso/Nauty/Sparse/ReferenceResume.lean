/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReferenceFilter
public import HexGraphIso.Nauty.Sparse.MaxNode
import all HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.Maximum
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The actual returned child, both literal filters and recovery supply
the next complete sweep context. Its maximum coverage comes from the
proved native search theorem, independently of generator completeness. -/
theorem SweepInput.received {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel tv tv1 : Nat} {l : Loop n} {bs fs : List Nat}
    {cell : VSet n} {st out : State n} {parents : Parents n} {short : Bool}
    (h : SweepInput G tcLevel l bs fs (some tv) cell st parents)
    (hbudget : n ≤ l.node.level + fuel) :
    let c := l.cell G.graph tcLevel
    let left := (policy (n := n)).leaveChild tv out
    let back := (policy (n := n)).recover (n + 2) l.node.level left
    let small := if short then (policy (n := n)).shortprune cell left else cell
    let filtered := if !l.first && tv == tv1 then (policy (n := n)).longprune small left else small
    Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (l.node.level + 1) (c.numcells + 1)
      ((policy (n := n)).child l.first l.node.level c.tc tv st) = (.unwind l.node.level short, out) →
    ∃ ds, SweepInput G tcLevel l ds fs (filtered.nextElem (some tv)) filtered back parents := by
  intro c left back small filtered hcall
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hv := h.member tv rfl
  let p := l.parent G.graph tcLevel st bs cell tv
  let ch := p.child G.graph tcLevel
  have hp : p.Valid G tcLevel := h.parent hv
  have hch := h.child rfl
  have hlen : ch.codes.length = l.node.level := by
    change (l.node.codes ++ [_]).length = l.node.level
    simp only [List.length_append, List.length_singleton, h.frame.length]
  have hmax := node_max G tcLevel fuel ch bs fs (parents.push p) hch (by rw [hlen]; exact hbudget)
  change MaxResult (ch.key G.graph tcLevel) (State.key G.graph bs ch.entry)
    (State.best G.graph (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (l.node.level + 1) (c.numcells + 1) ((policy (n := n)).child l.first l.node.level c.tc tv st)).2)
    l.node.level _ (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (l.node.level + 1) (c.numcells + 1) ((policy (n := n)).child l.first l.node.level c.tc tv st)).1 at hmax
  rw [hcall] at hmax
  have hcovered : Covers (ch.key G.graph tcLevel) (State.best G.graph out) := by
    simpa only [ExitCover, ↓reduceIte] using hmax.coverage.2
  obtain ⟨ds, hr, resumed⟩ := Scope.receive (p := p) h.scope hp h.codes h.machine h.recorded h.route hbudget
  have hbackEq : p.back G.graph tcLevel fuel = back := by
    change (policy (n := n)).recover (n + 2) l.node.level
      ((policy (n := n)).leaveChild tv (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
        (l.node.level + 1) (c.numcells + 1) ((policy (n := n)).child l.first l.node.level c.tc tv st)).2) = back
    rw [hcall]
  have hbackRead : State.best G.graph back = State.key G.graph ds back := by
    have hh : State.best G.graph back = State.best G.graph out :=
      recover_best G.graph (n + 2) l.node.level left
    have hread : State.best G.graph out = State.key G.graph ds out := by
      have hh := hr.read
      have hc : Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
          (p.child G.graph tcLevel).level (p.child G.graph tcLevel).numcells
          (p.child G.graph tcLevel).entry = (.unwind l.node.level short, out) := hcall
      rw [hc] at hh
      exact hh
    rw [hh, hread]
    exact (recover_key G.graph ds (n + 2) l.node.level left).symm
  have hpairs := node_pairs G hn tcLevel fuel ch.level ch.numcells ch.entry hch.frame.positive hch.pairs
  have hbackPairs := h.pairs.child_return hn h.frame.positive l.first fuel h.target hv h.recorded hpairs
  rw [hcall] at hbackPairs
  have hbackPairs' : PairsReady G tcLevel c.level c.numcells back := hbackPairs.1
  have hframe := hp.returned_frame (fuel := fuel) false
  change Ready G l.node.level c.numcells (p.back G.graph tcLevel fuel) ∧
    FrameOut G l.node.level l.node.level st (p.back G.graph tcLevel fuel) at hframe
  rw [hbackEq] at hframe
  have hbackFrame : FrameOut G c.level c.level c.entry back := h.effect.trans hframe.2
  have hvisit : c.Cover G.graph tcLevel (Remaining (cell.nextElem (some tv)) cell)
      (State.best G.graph left) :=
    h.cover.received h.selected h.effect h.pairs.ready (h.subset tv hv) hmax
  have hsmall : c.Cover G.graph tcLevel (Remaining (small.nextElem (some tv)) small)
      (State.best G.graph back) := by
    rw [recover_best]
    dsimp only [small]
    split
    · rename_i hshort
      have hs : short = true := hshort
      subst short
      have hshortCover := hvisit.short h.selected h.effect h.pairs h.target hv h.recorded
        h.counters.2.2 h.capacity (congrArg Prod.fst hcall) (Nat.le_refl _)
        (l.canon_guide h.selected h.effect h.codes.ready (h.guided tv))
        (fun v hv => h.subset v hv.1) (fun _ hv => hv.1)
      have hc : Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
          (c.level + 1) (c.numcells + 1) ((policy (n := n)).child l.first c.level c.tc tv st) =
            (.unwind l.node.level true, out) := hcall
      rw [hc] at hshortCover
      exact hshortCover.filtered (fun _ hm => shortprune_subset (st := left.frame) hm)
    · exact hvisit
  have hsmallSub : ∀ v, small.mem v = true → cell.mem v = true := by
    intro v hm
    dsimp only [small] at hm
    split at hm
    · exact shortprune_subset (st := left.frame) hm
    · exact hm
  have hfiltered : c.Cover G.graph tcLevel (Remaining (filtered.nextElem (some tv)) filtered)
      (State.best G.graph back) := by
    dsimp only [filtered]
    split
    · have hh := hsmall.long h.selected hbackFrame hbackPairs'
        (fun v hv => h.subset v (hsmallSub v hv.1)) (fun _ hv => hv.1)
      change c.Cover G.graph tcLevel
        (fun v => Remaining (small.nextElem (some tv)) small v ∧
          ((policy (n := n)).longprune small ((policy (n := n)).recover (n + 2) l.node.level left)).mem v = true)
        (State.best G.graph back) at hh
      rw [recover_long] at hh
      exact hh.filtered (fun _ hm => longprune_subset hm)
    · exact hsmall
  have hsub : ∀ v, filtered.mem v = true → cell.mem v = true := by
    intro v hm
    apply hsmallSub
    dsimp only [filtered] at hm
    split at hm
    · exact longprune_subset hm
    · exact hm
  have hcovered' : Covers (ch.key G.graph tcLevel)
      (State.best G.graph (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
        ch.level ch.numcells ch.entry).2) := by
    change Covers _ (State.best G.graph (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (l.node.level + 1) (c.numcells + 1) ((policy (n := n)).child l.first l.node.level c.tc tv st)).2)
    rw [hcall]
    exact hcovered
  rw [hbackRead] at hfiltered
  have hnext := h.recovered rfl hr resumed hcovered' hsub (by
    change c.Cover G.graph tcLevel (Remaining (filtered.nextElem (some tv)) filtered)
      (State.key G.graph ds (p.back G.graph tcLevel fuel))
    rw [hbackEq]
    exact hfiltered)
  change SweepInput G tcLevel l ds fs (filtered.nextElem (some tv)) filtered
    (p.back G.graph tcLevel fuel) parents at hnext
  rw [hbackEq] at hnext
  exact ⟨ds, hnext⟩

end Hex.GraphIso.Nauty.Sparse.Max
