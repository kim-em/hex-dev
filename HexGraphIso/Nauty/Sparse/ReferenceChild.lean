/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.PathCover
public import HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A reference in the frozen target child occurs in the exact cached
child entered by the production sweep, after any sibling reordering. -/
theorem SweepInput.reference_child {G : GraphIso.Sparse.Colored n k}
    {tcLevel boundary tv o : Nat} {l : Loop n} {bs fs : List Nat}
    {cell : VSet n} {st : State n} {parents : Parents n}
    {targets : List Nat} {key : Key n}
    (h : SweepInput G tcLevel l bs fs (some tv) cell st parents) :
    let c := l.cell G.graph tcLevel
    let R := State.refined (.ofGraph G.graph) l.node.level l.node.numcells l.node.entry
    let ch := (policy (n := n)).child l.first l.node.level c.tc tv st
    o < c.len → c.entry.lab[c.tc + o]! = tv →
      Generation.ChildPath G.graph tcLevel boundary l.node.level R c.tc targets key o →
        Generation.RefPath G.graph tcLevel boundary (l.node.level + 1)
          (State.refined (.ofGraph G.graph) (l.node.level + 1) (c.numcells + 1) ch) targets key := by
  intro c R ch ho hat href
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hr : RefineSt.Ready G.graph l.node.level R := h.frame.node.refined
  have hp : st.ptn = R.ptn := h.effect.effect.ptnEq h.selected.ready.ok h.codes.ready.ok
  have hperm : cellsPerm R.ptn l.node.level st.lab R.lab := cellsPerm_symm h.effect.effect.perm
  have hs : st.lab.size = R.lab.size := h.codes.ready.ok.labSize.trans hr.spec.node.labSize.symm
  have ht := hr.setLab st.lab hs hperm
  have hv : cell.mem tv = true := h.member tv rfl
  have hwindow : (windowSet n st.lab c.tc c.len).mem tv = true := by
    have he : windowSet n c.entry.lab c.tc c.len = windowSet n st.lab c.tc c.len :=
      h.effect.effect.window_eq h.selected.window
    rw [← he]
    exact h.subset tv hv
  obtain ⟨j, hj, hjv⟩ := mem_segN_iff.mp (mem_windowSet.mp hwindow).2
  have hchild := h.codes.ready.child hn h.frame.positive l.first h.target hv
  have hsc : Scratch.Bounded n ch.canong.scratch := hchild.scratch
  have hpath := (Generation.ChildPath.reorder (t := { R with lab := st.lab }) hr ht rfl hperm
    h.selected.window h.selected.range h.selected.size ho hj hsc (hjv.trans hat.symm)).mp href
  change Generation.RefPath G.graph tcLevel boundary (l.node.level + 1)
    (({ R with lab := st.lab } : RefineSt n).child (.ofGraph G.graph) l.node.level c.tc
      st.lab[c.tc + j]! ch.canong.scratch) targets key at hpath
  rw [hjv] at hpath
  have hvisit : State.refined (.ofGraph G.graph) (l.node.level + 1) (c.numcells + 1) ch =
      ({ R with lab := st.lab } : RefineSt n).child (.ofGraph G.graph) l.node.level c.tc tv
        ch.canong.scratch := by
    have hf := child_fields l.first l.node.level c.tc tv st
    unfold State.refined RefineSt.child
    rw [hf.1, hf.2.1, hf.2.2, hp]
    rfl
  rw [hvisit]
  exact hpath

end Hex.GraphIso.Nauty.Sparse.Max
