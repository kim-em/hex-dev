/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Preparation
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The real first-path target dispatch chooses the unhinted native
target, using its established indexed scratch and nonempty partition. -/
theorem Ready.first_choice {G : GraphIso.Sparse.Colored n k}
    {tcLevel level numcells : Nat} {st : State n}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level) (hc : numcells < n) :
    (chooseTarget true (.ofGraph G.graph) tcLevel level numcells st).1 =
      Int.ofNat (targetcell (.ofGraph G.graph) st.lab st.ptn level tcLevel (-1)) := by
  have hp := isPerm_of_cellsReach h.ok.labSize hn h.ok.reach
  obtain ⟨label, hlabel⟩ := Label.ofArray?_exists hp
  have hend : st.ptn[n - 1]! ≤ level := by
    have hs : st.ptn.size = n := h.ok.ptnSize
    simpa only [hs] using (h.partition hn hl).ptnEnd
  have hcount : bcount st.ptn level n < n := by
    have he : numcells = bcount st.ptn level n := h.ok.count
    omega
  have he := maketargetCached_eq G.graph st.lab st.ptn level tcLevel (-1) st.canong.scratch
    label hlabel h.ok.ptnSize hend h.scratch (Target.nonempty h.ok.ptnSize hend hcount)
  have hpos := congrArg (fun t : Nat × VSet n × Nat => t.1) he
  have hne : (numcells != n) = true := bne_iff_ne.mpr (by omega)
  simp only [chooseTarget, hne, Bool.not_true, Bool.false_and, Bool.false_eq_true,
    ite_true, ite_false, Id.run_pure]
  rw [hpos]
  rfl

/-- The mathematical target of the first descent is the actual cached
refinement's native target, with no conversion to dense refinement. -/
theorem prepareFirst_choice {G : GraphIso.Sparse.Colored n k}
    {tcLevel level numcells : Nat} {st : State n}
    (h : NodeInv G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hopen : (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).1 ≠ n) :
    (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).2.1 =
      Int.ofNat (targetcell (.ofGraph G.graph) (State.refined (.ofGraph G.graph) level numcells st).lab
        (State.refined (.ofGraph G.graph) level numcells st).ptn level tcLevel (-1)) := by
  have hv := h.visit_ready hn hl
  have hr := (hv.record (visit (.ofGraph G.graph) level numcells st).2.1).ready
  have hc : (visit (.ofGraph G.graph) level numcells st).1 < n := by
    have he := hv.ok.count
    change (visit (.ofGraph G.graph) level numcells st).1 =
      bcount (visit (.ofGraph G.graph) level numcells st).2.2.ptn level n at he
    have hb := bcount_le (visit (.ofGraph G.graph) level numcells st).2.2.ptn level n
    change (visit (.ofGraph G.graph) level numcells st).1 ≠ n at hopen
    omega
  exact hr.first_choice hn hl hc

end Hex.GraphIso.Nauty.Sparse
