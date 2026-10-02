/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReferenceChild
public import HexGraphIso.Nauty.Sparse.ReferenceSweep
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.CanonGuide
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Receiving a native off-path child advances reference coverage. A
canonical carrier comes from an earlier child; the other carrier kinds
return above this receiver. The child-reference implication is the local
premise supplied by the recursive reference-completion induction. -/
theorem SweepInput.reference_visit {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel boundary tv : Nat} {l : Loop n} {bs fs : List Nat}
    {cell : VSet n} {st out : State n} {parents : Parents n}
    {targets : List Nat} {key : Key n} {previous : Option Nat} {short : Bool}
    (h : SweepInput G tcLevel l bs fs (some tv) cell st parents) (hfirst : l.first = false) :
    let c := l.cell G.graph tcLevel
    let R := State.refined (.ofGraph G.graph) l.node.level l.node.numcells l.node.entry
    Generation.PathCover G.graph tcLevel boundary l.node.level R c.tc c.len targets key cell previous →
    Nauty.Generation.CanonPast l.node.level c.tc previous st →
    cell.nextElem previous = some tv →
    Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (l.node.level + 1) (c.numcells + 1)
      ((policy (n := n)).child l.first l.node.level c.tc tv st) = (.unwind l.node.level short, out) →
    (∀ o, o < c.len → R.lab[c.tc + o]! = tv →
      Generation.ChildPath G.graph tcLevel boundary l.node.level R c.tc targets key o →
        RefReturn (Graph.context G.graph) l.node.level out) →
    Generation.PathCover G.graph tcLevel boundary l.node.level R c.tc c.len targets key cell (some tv) := by
  intro c R hcover hpast hnext hcall hreceipt
  classical
  by_cases hex : ∃ o, o < c.len ∧ R.lab[c.tc + o]! = tv ∧
    Generation.ChildPath G.graph tcLevel boundary l.node.level R c.tc targets key o
  · obtain ⟨o, ho, hat, href⟩ := hex
    have hr := hreceipt o ho hat href
    have hg := node_gca (.ofGraph G.graph) (n + 2) tcLevel fuel (l.node.level + 1) (c.numcells + 1)
      ((policy (n := n)).child l.first l.node.level c.tc tv st)
    rw [hcall] at hg
    have hf : out.gcaFirst = st.gcaFirst := by
      rw [hfirst] at hg
      exact hg
    have hbefore := h.other hfirst
    cases hr with
    | first returned carrier => omega
    | orbit returned smaller => omega
    | canon returned carrier =>
      have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
      have hv := VSet.nextElem_mem hnext
      have hready : RefineSt.Ready G.graph l.node.level R := h.frame.node.refined
      have hearlier := h.codes.ready.canon_earlier (tcLevel := tcLevel) (fuel := fuel)
        hn h.frame.positive l.first false h.target hpast hnext
      rw [hcall] at hearlier
      have hguide := child_canon_locate (tcLevel := tcLevel) (fuel := fuel) h.codes.ready
        hn h.frame.positive l.first false h.target hv (h.guided tv).canonical
      rw [hcall] at hguide
      obtain ⟨v, _, hatv, hp⟩ := hguide returned.symm
      have hptn : st.ptn = R.ptn := h.effect.effect.ptnEq h.selected.ready.ok h.codes.ready.ok
      have hcanon : cellsPerm R.ptn l.node.level R.lab out.canonlab := by
        have hp' : cellsPerm st.ptn l.node.level st.lab out.canonlab := hp
        rw [hptn] at hp'
        exact cellsPerm_trans h.effect.effect.perm hp'
      have hm : out.canonlab[c.tc]! ∈ segN R.lab c.tc c.len :=
        (hcanon c.tc c.len h.selected.window).mem_iff.mpr
          (mem_segN_iff.mpr ⟨0, by have := h.selected.size; omega, by simp⟩)
      obtain ⟨oRef, hoRef, hatRef⟩ := mem_segN_iff.mp hm
      have hchild := h.codes.ready.child hn h.frame.positive l.first h.target hv
      have hout := node_frame G hn false tcLevel fuel (l.node.level + 1) (c.numcells + 1)
        ((policy (n := n)).child l.first l.node.level c.tc tv st) (by omega) hchild
      rw [hcall] at hout
      have hparent := h.codes.ready.child_frame hn h.frame.positive l.first h.target hv
        (by simpa only [Nat.add_sub_cancel] using hout)
      have hcurrent : cellsPerm R.ptn l.node.level R.lab out.lab :=
        (h.effect.trans hparent).effect.perm
      have hchosen := h.codes.ready.child_chosen (tcLevel := tcLevel) (fuel := fuel)
        hn h.frame.positive l.first false h.target hv
      rw [hcall] at hchosen
      have hentry := h.codes.child hn h.frame.positive l.first h.target hv h.recorded h.route
      have hsaved := hentry.saved.node hn tcLevel fuel (l.node.level + 1) (c.numcells + 1)
        (by omega) hchild
      rw [hcall] at hsaved
      have hcarrier : CellCarrier (Graph.context G.graph) R.ptn l.node.level R.lab
          out.canonlab out.lab out.genTrace := by
        obtain ⟨gamma, hmem, hcheck, hmap⟩ := carrier
        exact ⟨gamma, hmem, hcheck, hmap, cellStab_of_scatter hready.spec.node.ptnSize
          hready.spec.node.labSize hsaved.canonical.1 hready.spec.node.ptnEnd hcanon hcurrent hmap⟩
      exact Generation.PathCover.reference hcover hnext hready h.selected.window h.selected.range
        h.selected.size hoRef (by rw [hatRef]; exact hearlier returned.symm)
        hcarrier hatRef.symm hchosen
  · apply Generation.PathCover.advance hcover hnext
    intro o ho hat href
    exact hex ⟨o, ho, hat, href⟩

end Hex.GraphIso.Nauty.Sparse.Max
