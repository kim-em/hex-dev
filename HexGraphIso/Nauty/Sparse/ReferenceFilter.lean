/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReferenceVisit
public import HexGraphIso.Nauty.Sparse.ResumeCover
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Both filters after an actual off-path child preserve the richer
reference ledger. The complete native child call supplies receiver pair
validity; the recovered partition transports it to the frozen target. -/
theorem SweepInput.reference_filters {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel boundary tv tv1 : Nat} {l : Loop n} {bs fs : List Nat}
    {cell : VSet n} {st out : State n} {parents : Parents n}
    {targets : List Nat} {key : Key n} {short : Bool}
    (h : SweepInput G tcLevel l bs fs (some tv) cell st parents) :
    let c := l.cell G.graph tcLevel
    let R := State.refined (.ofGraph G.graph) l.node.level l.node.numcells l.node.entry
    let left := (policy (n := n)).leaveChild tv out
    let small := if short then (policy (n := n)).shortprune cell left else cell
    let filtered := if !l.first && tv == tv1 then (policy (n := n)).longprune small left else small
    Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (l.node.level + 1) (c.numcells + 1)
      ((policy (n := n)).child l.first l.node.level c.tc tv st) = (.unwind l.node.level short, out) →
    Generation.PathCover G.graph tcLevel boundary l.node.level R c.tc c.len targets key cell (some tv) →
    Generation.PathCover G.graph tcLevel boundary l.node.level R c.tc c.len targets key filtered (some tv) := by
  intro c R left small filtered hcall hcover
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hr : RefineSt.Ready G.graph l.node.level R := h.frame.node.refined
  have hbound : c.tc + c.len ≤ n := h.selected.range
  have hv := h.member tv rfl
  have hch := h.pairs.child hn h.frame.positive l.first h.target hv h.recorded
  have hpairs := node_pairs G hn tcLevel fuel (l.node.level + 1) (c.numcells + 1)
    ((policy (n := n)).child l.first l.node.level c.tc tv st) (by omega) hch
  have hbackPairs := h.pairs.child_return hn h.frame.positive l.first fuel h.target hv h.recorded hpairs
  rw [hcall] at hbackPairs
  let back := (policy (n := n)).recover (n + 2) l.node.level left
  have hp : PairsReady G tcLevel l.node.level c.numcells back := hbackPairs.1
  have hx := node_frame G hn false tcLevel fuel (l.node.level + 1) (c.numcells + 1)
    ((policy (n := n)).child l.first l.node.level c.tc tv st) (by omega) hch.node
  rw [hcall] at hx
  have hparent := h.codes.ready.child_frame hn h.frame.positive l.first h.target hv
    (by simpa only [Nat.add_sub_cancel] using hx)
  have hback : FrameOut G l.node.level l.node.level c.entry back :=
    h.effect.trans (h.codes.ready.recover hn h.frame.positive (hparent.leave tv)).2
  have hsmall : Generation.PathCover G.graph tcLevel boundary l.node.level R c.tc c.len
      targets key small (some tv) := by
    dsimp only [small]
    split
    · rename_i hshort
      have hs : short = true := hshort
      subst short
      apply Generation.PathCover.filterAutom hcover hr h.selected.window h.selected.range h.selected.size
        ?_ (fun _ hm => shortprune_subset (st := left.frame) hm)
      intro o ho hm
      have hdrop := h.pairs.short_drop hn h.frame.positive h.target hv h.recorded h.counters.2.2
        h.capacity (congrArg Prod.fst hcall) (Nat.le_refl _) (h.guided tv).canonical
      rw [hcall] at hdrop
      obtain ⟨gamma, ha, hstab, hlt⟩ := hdrop R.lab[c.tc + o]!
        (perm_bound hr.spec.label (by have := ho.1; omega)) ho.2.1 hm
      exact ⟨gamma, ha, h.selected.stabilizes h.effect h.pairs.ready hstab, hlt⟩
    · exact hcover
  dsimp only [filtered]
  split
  · have hlong := recover_long (n + 2) l.node.level left small
    change (policy (n := n)).longprune small back = (policy (n := n)).longprune small left at hlong
    rw [← hlong]
    apply Generation.PathCover.filterAutom hsmall hr h.selected.window h.selected.range h.selected.size
      ?_ (fun _ hm => longprune_subset hm)
    intro o ho hm
    obtain ⟨gamma, ha, hstab, hlt⟩ := hp.long_drop
      (perm_bound hr.spec.label (by have := ho.1; omega)) ho.2.1 hm
    exact ⟨gamma, ha, h.selected.stabilizes hback hp.ready hstab, hlt⟩
  · exact hsmall

end Hex.GraphIso.Nauty.Sparse.Max
