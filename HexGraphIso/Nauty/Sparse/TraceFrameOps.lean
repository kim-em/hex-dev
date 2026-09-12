/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TraceFrameLeaf
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Cached target selection does not append to or replace the trace. -/
theorem chooseTarget_trace (first : Bool) (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (chooseTarget first g tcLevel level numcells st).2.2.2.genTrace = st.genTrace := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n => out.2.2.2.genTrace = st.genTrace)
  mvcgen
  all_goals simp_all +zetaDelta

namespace TraceFrame

variable {G : GraphIso.Sparse.Colored n k} {base cells level numcells : Nat} {root st : State n}

/-- A native visit below the frozen ancestor preserves its references
and trace while refining the current partition inside the ancestor cells. -/
theorem visit (h : TraceFrame G base root st) (hp : Ready G base cells root)
    (hi : NodeInv G level numcells st) (hn : 0 < n) (hb : 1 ≤ base) (hlevel : base < level) :
    TraceFrame G base root (Sparse.visit (.ofGraph G.graph) level numcells st).2.2 := by
  have hl : 1 ≤ level := by omega
  have hr := hi.visit_ready hn hl
  have he := hi.visit_frame hl ⟨SearchOut.refl _ _ _ hr.ok.reach, hr.scratch.toBounded⟩
  exact h.extend hp hn hb he (by omega) (by omega) h.trace h.work

theorem record (h : TraceFrame G base root st) (level code : Nat) :
    TraceFrame G base root (recordFirst level code st) :=
  h.fields rfl rfl rfl rfl rfl rfl h.frame.scratch

theorem compare (h : TraceFrame G base root st) (level code : Nat) :
    TraceFrame G base root (compareCodes level code st) := by
  obtain ⟨hl, hp, hf, hc⟩ := compareCodes_frame level code st
  apply h.fields hl hp hf hc
  · unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.genTrace, ite_self]
  · unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite (fun s : State n => s.workperm.size), ite_self]
  · rw [SearchState.compare_storage]
    exact h.frame.scratch

theorem target (h : TraceFrame G base root st) (first : Bool) (tcLevel level numcells : Nat) :
    TraceFrame G base root (chooseTarget first (.ofGraph G.graph) tcLevel level numcells st).2.2.2 := by
  obtain ⟨hl, hp, hf, hc⟩ := chooseTarget_frame first (.ofGraph G.graph) tcLevel level numcells st
  exact h.fields hl hp hf hc (chooseTarget_trace ..) (chooseTarget_workSize ..)
    (chooseTarget_bounded first (.ofGraph G.graph) tcLevel level numcells st h.frame.scratch)

theorem cheap (h : TraceFrame G base root st) (first : Bool) (level : Nat) :
    TraceFrame G base root (cheapCheck first level st) := by
  unfold cheapCheck
  split <;> exact h.fields rfl rfl rfl rfl rfl rfl h.frame.scratch

/-- Installing a first leaf places both references in the current labels,
which the incoming frame already locates inside the suspended ancestor. -/
theorem terminal (h : TraceFrame G base root st) (hp : Ready G base cells root)
    (hr : Ready G level numcells st) (hn : 0 < n) (hb : 1 ≤ base) (hlevel : base ≤ level) :
    TraceFrame G base root (firstterminal level st) :=
  h.extend hp hn hb hr.terminal.frame hlevel hlevel h.trace h.work

/-- Actual individualization stays inside every suspended ancestor frame,
retaining its references and all previously emitted stabilizers. -/
theorem child (h : TraceFrame G base root st) (hp : Ready G base cells root)
    (hr : Ready G level numcells st) (hn : 0 < n) (hb : 1 ≤ base) (hlevel : base ≤ level)
    (first : Bool) {tc tv : Nat} {cell : VSet n}
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    TraceFrame G base root ((policy (n := n)).child first level tc tv st) := by
  have hl : 1 ≤ level := by omega
  have hi := hr.child hn hl first ht hv
  have he := hr.child_frame hn hl first ht hv (FrameOut.refl hi)
  apply h.extend hp hn hb he hlevel hlevel
  · cases first <;> exact h.trace
  · cases first <;> exact h.work

theorem afterChild (h : TraceFrame G base root st) (level tv : Nat) :
    TraceFrame G base root (afterChildFirst level tv st) :=
  h.fields rfl rfl rfl rfl rfl rfl h.frame.scratch

theorem leave (h : TraceFrame G base root st) (tv : Nat) :
    TraceFrame G base root ((policy (n := n)).leaveChild tv st) :=
  h.fields rfl rfl rfl rfl rfl rfl h.frame.scratch

/-- Recovering a still-active ancestor preserves every coarser frozen
frame and its references; the invalidated sparse cache retains its bounds. -/
theorem recover (h : TraceFrame G base root st) (hp : Ready G base cells root)
    (hn : 0 < n) (hb : 1 ≤ base) (hlevel : base ≤ level) (hbound : level ≤ n) :
    TraceFrame G base root ((policy (n := n)).recover (n + 2) level st) := by
  have he : FrameOut G level level st ((policy (n := n)).recover (n + 2) level st) := by
    refine ⟨?_, (recover_valid (n + 2) level st h.frame.scratch).toBounded⟩
    rw [State.recover_frame]
    exact recover_out (by omega) h.frame.effect.reach
  apply h.extend hp hn hb he hlevel hlevel
  · change ∀ gamma ∈ (recoverLevels level (recoverPtn (n + 2) level st)).genTrace,
      CellStab root.ptn base root.lab gamma
    unfold recoverLevels recoverPtn
    simpa only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.genTrace, ite_self]
      using h.trace
  · exact (workSizePolicy (.ofGraph G.graph) (n + 2) 0 n).recover level st h.work

theorem afterSweep (h : TraceFrame G base root st) (first : Bool) (level size index : Nat) :
    TraceFrame G base root ((policy (n := n)).afterSweep first level size index st) := by
  change TraceFrame G base root (if first then
    { (Nauty.afterSweep first level size index st) with
      order := (Nauty.afterSweep first level size index st).order * index }
    else Nauty.afterSweep first level size index st)
  cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals unfold Nauty.afterSweep; split <;> exact h.fields rfl rfl rfl rfl rfl rfl h.frame.scratch

end TraceFrame
end Hex.GraphIso.Nauty.Sparse
