/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.VertexFrame
public import HexGraphIso.Nauty.Sparse.RefineTransport
public import HexGraphIso.Nauty.Sparse.VisitFrame
import all HexGraphIso.Nauty.Spec.SpecIso
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The actual cached visit and the fresh visit used by the unpruned
specification have identical codes, counts and partitions, with labels
permuted within their ordered cells. This supplies the parent frame needed
to transport whole child maxima without requiring identical label arrays. -/
theorem NodeInv.visit_equiv {G : GraphIso.Sparse.Colored n k} {level numcells : Nat}
    {st : State n} (h : NodeInv G level numcells st) (hn : 0 < n) (hl : 1 ≤ level) :
    let fresh : State n := { st with canong := { st.canong with scratch := .fresh n } }
    let f := visit (.ofGraph G.graph) level numcells fresh
    let r := visit (.ofGraph G.graph) level numcells st
    f.1 = r.1 ∧ f.2.1 = r.2.1 ∧ r.2.2.ptn = f.2.2.ptn ∧
      FrameOut G level level f.2.2 r.2.2 ∧
      Ready G level f.1 f.2.2 ∧ Ready G level r.1 r.2.2 := by
  intro fresh f r
  have hb := (Scratch.fresh_valid n st.lab st.ptn level).toBounded
  have hfresh : NodeInv G level numcells fresh := ⟨h.spec, h.ok, hb⟩
  have hfr := hfresh.visit_ready hn hl
  have hrr := h.visit_ready hn hl
  have hid : (renamingOf (Perm.id n)).toFun = id := by funext v; simp [renamingOf]
  have hcell : cellsPerm st.ptn level st.lab (st.lab.map (renamingOf (Perm.id n)).toFun) := by
    rw [hid, Array.map_id]
    exact cellsPerm_refl _ _ _
  have hend : st.ptn[n - 1]! ≤ level := by simpa only [h.spec.node.ptnSize] using h.spec.node.ptnEnd
  have he := refineWith_equiv G.graph G.graph (Perm.id n)
    (by intros; simp only [Perm.get_id]) level st.lab st.lab st.ptn st.active numcells
    (.fresh n) st.canong.scratch h.spec.label h.spec.label h.spec.node.ptnSize hend h.spec.node.starts
    hb h.scratch hcell
  have hp : r.2.2.ptn = f.2.2.ptn := he.ptn
  have hc := he.cells
  rw [hid, Array.map_id] at hc
  have hperm : cellsPerm f.2.2.ptn level f.2.2.lab r.2.2.lab := cellsPerm_symm hc
  refine ⟨he.count, he.code, hp, ?_, hfr, hrr⟩
  refine ⟨⟨hrr.ok.labSize.trans hfr.ok.labSize.symm, congrArg Array.size hp,
    hrr.ok.reach, ?_, hperm, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩, hrr.scratch.toBounded⟩
  intro q _
  exact congrArg (fun ptn : Array Nat => ptn[q]!) hp

end Hex.GraphIso.Nauty.Sparse
