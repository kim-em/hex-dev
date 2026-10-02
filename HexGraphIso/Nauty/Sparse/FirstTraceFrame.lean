/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TraceFrameSeed
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A successful actual first descent initializes the frozen ancestor's
reference and generator invariant, then preserves it through every later
child and return. Only the incoming empty trace and workspace allocation
are assumed; reference containment is derived from the installed first leaf. -/
theorem firstPath_stabilizes {G : GraphIso.Sparse.Colored n k}
    {base cells : Nat} {root : State n} (hp : Ready G base cells root)
    (hn : 0 < n) (hb : 1 ≤ base)
    {tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel level numcells st last leaf)
    (hlevel : base < level) (hi : NodeInv G level numcells st)
    (hframe : FrameOut G base base root st) (hwork : st.workperm.size = n) (htrace : st.genTrace = #[]) :
    TraceFrame G base root
      (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    have hl : 1 ≤ level := by omega
    have hr := (hi.prepare (tcLevel := tcLevel) hn hl).1
    have hf := hframe.extend (hi.prepare_frame hn hl tcLevel) hp hn hb (by omega) (by omega)
    have hterminal := hf.first_seed hp hr hn hb (by omega)
      ((prepareFirst_trace (.ofGraph G.graph) tcLevel level numcells st).trans htrace)
      ((prepareFirst_workSize (.ofGraph G.graph) tcLevel level numcells st).trans hwork)
    unfold Generic.prepareFirst at hdisc hterminal
    dsimp only at hdisc
    rw [Generic.node]
    unfold Generic.nodeStep
    dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
      Generic.Policy.chooseTarget, Generic.Policy.firstterminal] at hdisc hterminal ⊢
    simpa only [ite_true, hdisc, beq_self_eq_true, Id.run_pure] using hterminal
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    have hl : 1 ≤ level := by omega
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    let ready := cheapCheck true level r.2.2.2.2
    let ch := (policy (n := n)).child true level r.2.1.toNat tv ready
    let raw := Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1) ch
    let left := (policy (n := n)).leaveChild tv (afterChildFirst level tv raw.2)
    obtain ⟨hr, ht⟩ := hi.prepare (tcLevel := tcLevel) hn hl
    have hready := hr.cheap true
    have htarget := ht.of_out hready.frame.effect
    have hmem := VSet.nextElem_mem htv
    have hch := hready.ready.child hn hl true htarget hmem
    have hprep := hframe.extend (hi.prepare_frame hn hl tcLevel) hp hn hb (by omega) (by omega)
    have hreadyFrame := hprep.extend hready.frame hp hn hb (by omega) (by omega)
    have hchildFrame := hreadyFrame.extend
      (hready.ready.child_frame hn hl true htarget hmem (FrameOut.refl hch))
      hp hn hb (by omega) (by omega)
    have hcw : ch.workperm.size = n := by
      change ready.workperm.size = n
      unfold ready cheapCheck
      split <;> exact (prepareFirst_workSize (.ofGraph G.graph) tcLevel level numcells st).trans hwork
    have hct : ch.genTrace = #[] := by
      change ready.genTrace = #[]
      unfold ready cheapCheck
      split <;> exact (prepareFirst_trace (.ofGraph G.graph) tcLevel level numcells st).trans htrace
    have hchild : TraceFrame G base root raw.2 := ih (by omega) hch hchildFrame hcw hct
    have ho := node_frame G hn true tcLevel fuel (level + 1) (r.1 + 1) ch (by omega) hch
    have hf := hready.ready.child_frame hn hl true htarget hmem
      (by simpa only [Nat.add_sub_cancel] using ho)
    let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
      Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel n level numcells tc tv1 cursor cell index st
    have hnxt : (traceFrameContract G base root).sweepValid fuel n next :=
      fun first level numcells tc tv1 cursor cell index st hin =>
        Generic.sweep_sound (traceFramePolicy G hp hn hb tcLevel) first fuel n
          level numcells tc tv1 cursor cell index st hin
    have hadv := traceFrame_advance G hp hn hb hnxt true level r.1 r.2.1.toNat tv tv 0 r.2.2.1
      ready left raw.1 hl hready.ready htarget ((hf.afterChild level tv).leave tv) (by omega)
      ((hchild.afterChild level tv).leave tv)
    have hsweep : TraceFrame G base root
        (Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
          level r.1 r.2.1.toNat tv (some tv) r.2.2.1 0 ready).2.2 := by
      have horbit' : Generic.Policy.orbit (n := n) ready tv = tv := horbit
      rw [Generic.sweep]
      unfold Generic.sweepStep
      simp only [Bool.not_true, horbit', beq_self_eq_true, Bool.or_true, Bool.and_self, ite_true]
      exact hadv
    rw [Generic.node]
    unfold Generic.nodeStep
    change TraceFrame G base root (Id.run do
      let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      if r.1 == n then
        return (.unwind (level - 1) false, Generic.Policy.firstterminal (n := n) level r.2.2.2.2)
      let s := Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        level r.1 r.2.1.toNat ((r.2.2.1.nextElem none).getD 0) (r.2.2.1.nextElem none) r.2.2.1 0
        (Generic.Policy.cheapCheck (n := n) true level r.2.2.2.2)
      match s.1 with
      | .done => return (.unwind (level - 1) false,
          Generic.Policy.afterSweep (n := n) true level r.2.2.2.1 s.2.1 s.2.2)
      | _ => return (s.1, s.2.2)).2
    simp only [beq_eq_false_iff_ne.mpr hopen, Bool.false_eq_true, ite_false, htv, Option.getD_some]
    generalize he : Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
      level r.1 r.2.1.toNat tv (some tv) r.2.2.1 0
      (Generic.Policy.cheapCheck (n := n) true level r.2.2.2.2) = result at hsweep ⊢
    obtain ⟨exit, index, out⟩ := result
    cases exit with
    | fuel => exact hsweep
    | unwind => exact hsweep
    | done => exact hsweep.afterSweep true level r.2.2.2.1 index

end Hex.GraphIso.Nauty.Sparse
