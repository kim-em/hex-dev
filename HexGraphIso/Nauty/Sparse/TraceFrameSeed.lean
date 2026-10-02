/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TraceFrameCalls
public import HexGraphIso.Nauty.Sparse.FirstTrace
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Preparing a first node emits no generators. -/
theorem prepareFirst_trace (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2.genTrace = st.genTrace :=
  chooseTarget_trace true g tcLevel level (visit g level numcells st).1
    (recordFirst level (visit g level numcells st).2.1 (visit g level numcells st).2.2)

/-- Actual first preparation has the native node frame effect before
any child or terminal action occurs. -/
theorem NodeInv.prepare_frame {G : GraphIso.Sparse.Colored n k}
    {level numcells : Nat} {st : State n} (h : NodeInv G level numcells st)
    (hn : 0 < n) (hl : 1 ≤ level) (tcLevel : Nat) :
    FrameOut G (level - 1) level st
      (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).2.2.2.2 := by
  have hv := h.visit_ready hn hl
  have hr := hv.record (visit (.ofGraph G.graph) level numcells st).2.1
  exact h.visit_frame hl (hr.trans (hr.ready.target_frame true tcLevel)).frame

/-- The first terminal action seeds both reference frames from the actual
leaf label and the empty incoming trace. No reference containment is
assumed before the first leaf has been installed. -/
theorem FrameOut.first_seed {G : GraphIso.Sparse.Colored n k}
    {base cells level numcells : Nat} {root st : State n}
    (h : FrameOut G base base root st) (hp : Ready G base cells root)
    (hr : Ready G level numcells st) (hn : 0 < n) (hb : 1 ≤ base) (hlevel : base ≤ level)
    (ht : st.genTrace = #[]) (hw : st.workperm.size = n) :
    TraceFrame G base root (firstterminal level st) := by
  refine ⟨h.extend hr.terminal.frame hp hn hb hlevel hlevel,
    ⟨hr.ok.labSize, h.effect.perm⟩, ⟨hr.ok.labSize, h.effect.perm⟩, ?_, hw⟩
  intro gamma hg
  change gamma ∈ st.genTrace at hg
  rw [ht] at hg
  simp at hg

end Hex.GraphIso.Nauty.Sparse
