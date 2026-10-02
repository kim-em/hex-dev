/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxRetain
public import HexGraphIso.Nauty.Sparse.MaxScatter
import all HexGraphIso.Nauty.Sparse.MaxAncestor
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Every actual emitter remains inside each suspended selected child.
Its labelling therefore retains the chosen vertex at that target position.
The ancestor chain supplies both the cell permutation and the literal
closed boundaries needed to coarsen the final native refinement. -/
theorem Scope.emit_store {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs : List Nat} {st : State n} {parents : Parents n}
    (h : Scope G tcLevel f bs st parents) (hf : f.Valid G) {t : Nat} {p : Parent n}
    (hp : parents t = some p) :
    let out := (f.emit G.graph tcLevel).2
    out.lab.size = p.state.lab.size ∧ cellsPerm p.state.ptn p.node.level p.state.lab out.lab ∧
      out.lab[p.tc]! = p.chosen := by
  let ch := p.child G.graph tcLevel
  let out := (f.emit G.graph tcLevel).2
  obtain ⟨ht, htl, hlevel, hpv⟩ := h.valid t p hp
  have hn : 0 < n := by have := hf.positive; have := hf.depth; omega
  have hc : ch.Valid G := hpv.child
  have hx := h.child_frame hf hp
  have ho := hf.emit_frame (tcLevel := tcLevel)
  have hperm : cellsPerm ch.entry.ptn ch.level f.entry.lab out.lab := by
    apply cellsPerm_coarsen (hc.node.ok.ptnSize.trans hf.node.ok.ptnSize.symm)
      (hf.node.ok.labSize.trans hf.node.ok.ptnSize.symm)
      (ho.effect.labSize.trans (hf.node.ok.labSize.trans hf.node.ok.ptnSize.symm)) ho.effect.perm
      (searchOk_end hn hf.node.ok hf.positive) (searchOk_end hn hc.node.ok hc.positive)
    intro q hq
    have he := h.child_closed hp hq
    change f.entry.ptn[q]! ≤ f.level
    rw [he]
    change (p.child G.graph tcLevel).entry.ptn[q]! ≤ p.node.level + 1 at hq
    omega
  exact hpv.ready.child_store hn hpv.node.positive p.first hpv.target hpv.chosen
    ⟨ho.effect.labSize.trans hx.effect.labSize, cellsPerm_trans hx.effect.perm hperm⟩

/-- A scatter at the actual emitter covers the chosen child of a saved
ancestor. All current-label containment and selected-position facts are
derived from the native scope, rather than assumed by this return rule. -/
theorem Scope.emit_cover {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs : List Nat} {st : State n} {parents : Parents n}
    (h : Scope G tcLevel f bs st parents) (hf : f.Valid G) {t : Nat} {p : Parent n}
    (hp : parents t = some p) {ref gamma : Array Nat} {best : Option (Key n)}
    (ha : Automorphism G gamma) (href : ref.size = n)
    (hfr : cellsPerm p.state.ptn p.node.level p.state.lab ref)
    (hmap : ∀ i, i < n → gamma[ref[i]!]! = (f.emit G.graph tcLevel).2.lab[i]!)
    (hcover : Covers (p.key G.graph tcLevel ref[p.tc]!) best) :
    Covers ((p.child G.graph tcLevel).key G.graph tcLevel) best := by
  have hv := (h.valid t p hp).2.2.2
  have hl := h.emit_store hf hp
  exact hv.scatter_cover ha href hfr hl.2.1 hmap hl.2.2 hcover

/-- Coverage of a suspended selected child supplies exactly the frozen
ancestor named by a nonlocal return, using the retained parent chain. -/
theorem Scope.child_witness {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs : List Nat} {st : State n} {parents : Parents n}
    (h : Scope G tcLevel f bs st parents) {t : Nat} {p : Parent n}
    (hp : parents t = some p) (ht : t < f.level - 1) {best : Option (Key n)}
    (hc : Covers ((p.child G.graph tcLevel).key G.graph tcLevel) best) :
    Witness G tcLevel parents.frames t best := by
  have hpos := (h.valid t p hp).1
  obtain ⟨next, hnext⟩ := h.complete (t + 1) (by omega) (by omega)
  obtain ⟨prev, hv, hchild⟩ := h.chain (t + 1) next hnext (by omega)
  simp only [Nat.add_sub_cancel] at hv
  have hprev : prev = p := Option.some.inj (hv.symm.trans hp)
  rw [hprev] at hchild
  refine ⟨next.node, ?_, (h.valid (t + 1) next hnext).2.2.2.node, Or.inl ?_⟩
  · simp only [Parents.frames, hnext, Option.map_some]
  · rwa [← hchild]

end Hex.GraphIso.Nauty.Sparse.Max
