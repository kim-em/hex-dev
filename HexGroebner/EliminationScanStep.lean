/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
import all HexGroebner.MatrixStateProof
import all HexGroebner.EliminationOutcome
import all HexGroebner.EliminationPhaseProof
public import HexGroebner.EliminationPhaseProof

public section

/-! Owning scan correspondence proofs inspect private phase bodies. Do not
expose public unchecked State builders from this module. -/

namespace Hex.Groebner

private noncomputable def scanState (base : MatrixState.State) (data : Native.Scan.State)
    (quanta : Nat) (stats : MatrixStats) : MatrixState.State :=
  { base with phase := .scan,scan := data,quanta,stats }

private noncomputable def zeroScanned (base : MatrixState.State) (data : Native.Scan.State)
    (quanta : Nat) (stats : MatrixStats) : MatrixState.State :=
  (MatrixState.zeroRow.run { base with
    dense := data.dense
    scan := { data with dense := {} }
    sugar := data.sugar
    quanta := quanta
    stats := stats }).2

private theorem scan_zero (state : MatrixState.State) (hphase : state.phase = .scan)
    (hgeometry : state.geometry) (hquanta : state.quanta = 0) :
    outcome state = (.error .rowUpdate,state.stats) := by
  apply outcome_error state state .rowUpdate hgeometry (by simp [hphase])
  simp [MatrixState.step,hphase,hquanta,ExceptT.run,ExceptT.mk,ExceptT.bind,ExceptT.bindCont,
    ExceptT.lift,StateT.bind,StateT.get,StateT.pure,Bind.bind,MonadState.get,
    MonadStateOf.get,MonadExcept.throw,MonadExceptOf.throw,liftM,
    MonadLiftT.monadLift,MonadLift.monadLift,getThe,throwThe,StateT.map,Functor.map,Pure.pure]

set_option linter.unusedSimpArgs false in
private theorem scan_complete_zero (state : MatrixState.State) (output : Native.Scan.Result)
    (stats : MatrixStats) (hphase : state.phase = .scan) (hgeometry : state.geometry)
    (hquanta : state.quanta ≠ 0)
    (houtput : Native.Scan.portable state.field.modulus state.slots state.nativePivots state.scan
      4096 (state.limits.work-state.stats.work) 0 false = output)
    (hwork : (Matrix.work state.limits output.work).run state.stats = (.ok (),stats))
    (hstatus : output.status = 1) (hleading : output.state.leading = 0) :
    outcome state = outcome (zeroScanned state output.state (state.quanta-1)
      { stats with reductions := stats.reductions+output.reductions }) := by
  have zeroFormula := fun state => zero_run state
  simp only [ExceptT.run] at zeroFormula hwork
  rw [outcome_run state hgeometry (by simp [hphase])]
  simp [MatrixState.step,MatrixState.takeScan,MatrixState.work,zeroScanned,hphase,hquanta,
    houtput,hwork,hstatus,hleading,Native.Scan.transition,ExceptT.run,ExceptT.mk,ExceptT.pure,
    ExceptT.bind,ExceptT.bindCont,ExceptT.lift,StateT.bind,StateT.get,StateT.set,StateT.pure,
    Bind.bind,MonadState.get,MonadStateOf.get,MonadStateOf.set,liftM,MonadLiftT.monadLift,
    MonadLift.monadLift,getThe,StateT.map,Functor.map,Pure.pure,Id.run,modify,modifyGet,
    modifyThe,MonadStateOf.modifyGet,StateT.modifyGet,MatrixState.liftWork,zeroFormula]
  all_goals (try split) <;> try simp_all [zeroFormula]
  all_goals grind

private noncomputable def gatheredScan (base : MatrixState.State) (data : Native.Scan.State)
    (inverse : UInt64) (stats : MatrixStats) : MatrixState.State :=
  { base with
    phase := .gather
    scan := { data with dense := {} }
    gather := ⟨data.dense,{},{},data.leading-1⟩
    leading := data.leading-1
    sugar := data.sugar
    inverse := inverse
    quanta := (data.last+1-(data.leading-1)+4095)/4096+1
    stats := stats }

set_option linter.unusedSimpArgs false in
private theorem scan_complete_gather (state : MatrixState.State) (output : Native.Scan.Result)
    (workStats inverseStats stats : MatrixStats) (inverse : UInt64)
    (hphase : state.phase = .scan) (hgeometry : state.geometry) (hquanta : state.quanta ≠ 0)
    (houtput : Native.Scan.portable state.field.modulus state.slots state.nativePivots state.scan
      4096 (state.limits.work-state.stats.work) 0 false = output)
    (hwork : (Matrix.work state.limits output.work).run state.stats = (.ok (),workStats))
    (hstatus : output.status = 1) (hleading : output.state.leading ≠ 0)
    (hinverse : (if state.independent && MatrixState.isTarget state then (pure 1 : Matrix.Work UInt64)
        else Matrix.inverse state.field state.field.barrett state.limits
          (Packed.read state.field.width output.state.dense (output.state.leading-1))).run
        { workStats with reductions := workStats.reductions+output.reductions } = (.ok inverse,inverseStats))
    (hgather : (Matrix.work state.limits (output.state.last+1-(output.state.leading-1))).run
      inverseStats = (.ok (),stats)) :
    outcome state = outcome (gatheredScan state output.state inverse stats) := by
  simp only [ExceptT.run] at hwork hinverse hgather
  by_cases independent : state.independent = true ∧ MatrixState.isTarget state = true
  all_goals first
    | (simp only [Bool.and_eq_true,ite_eq_left independent] at hinverse
       change (Except.ok (1 : UInt64),
         { workStats with reductions := workStats.reductions+output.reductions }) =
         (.ok inverse,inverseStats) at hinverse
       obtain ⟨hinv,hstats⟩ := Prod.mk.inj hinverse
       cases Except.ok.inj hinv
       cases hstats)
    | simp only [Bool.and_eq_true,ite_eq_right independent] at hinverse
  all_goals rw [outcome_run state hgeometry (by simp [hphase])]
  all_goals simp [MatrixState.step,MatrixState.takeScan,MatrixState.work,gatheredScan,independent,hphase,hquanta,
    houtput,hwork,hstatus,hleading,hinverse,hgather,Native.Scan.transition,ExceptT.run,ExceptT.mk,
    ExceptT.pure,ExceptT.bind,ExceptT.bindCont,ExceptT.lift,StateT.bind,StateT.get,StateT.set,StateT.pure,
    Bind.bind,MonadState.get,MonadStateOf.get,MonadStateOf.set,liftM,MonadLiftT.monadLift,
    MonadLift.monadLift,getThe,StateT.map,Functor.map,Pure.pure,Id.run,modify,modifyGet,
    modifyThe,MonadStateOf.modifyGet,StateT.modifyGet,MatrixState.liftWork]
  all_goals (try split) <;> try simp_all [ExceptT.pure,Pure.pure,StateT.pure,StateT.bind,
    Bind.bind,ExceptT.bindCont,StateT.map,Functor.map,MonadStateOf.modifyGet,StateT.modifyGet]
  all_goals grind

private noncomputable def scanPending (state : MatrixState.State) (output : Native.Scan.Result)
    (stats : MatrixStats) : Except MatrixError (Echelon × Array RemainderRow) × MatrixStats :=
  if output.status == 2 then (.error (.exhausted .work),stats)
  else if output.status == 3 then (.error (.exhausted .traceNodes),stats)
  else if output.status != 0 && output.status != 1 then (.error .rowUpdate,stats)
  else if output.status == 0 && state.quanta == 1 then (.error .rowUpdate,stats)
  else outcome (scanState state output.state (state.quanta-1) stats)

set_option linter.unusedSimpArgs false in
private theorem scan_pending (state : MatrixState.State) (hphase : state.phase = .scan)
    (hgeometry : state.geometry) (hquanta : state.quanta ≠ 0)
    (hstatus : (Native.Scan.portable state.field.modulus state.slots state.nativePivots state.scan
      4096 (state.limits.work-state.stats.work) 0 false).status ≠ 1) :
    let output := Native.Scan.portable state.field.modulus state.slots state.nativePivots state.scan
      4096 (state.limits.work-state.stats.work) 0 false
    outcome state = match (Matrix.work state.limits output.work).run state.stats with
      | (.error error,stats) => (.error error,stats)
      | (.ok _,stats) => scanPending state output
          { stats with reductions := stats.reductions+output.reductions } := by
  dsimp only
  rw [outcome_run state hgeometry (by simp [hphase])]
  simp [MatrixState.step,MatrixState.takeScan,MatrixState.work,hphase,hquanta,
    scanPending,scanState,ExceptT.run,ExceptT.mk,ExceptT.pure,ExceptT.bind,ExceptT.bindCont,
    ExceptT.lift,StateT.bind,StateT.get,StateT.set,StateT.pure,Bind.bind,MonadState.get,
    MonadStateOf.get,MonadStateOf.set,MonadExcept.throw,MonadExceptOf.throw,liftM,
    MonadLiftT.monadLift,MonadLift.monadLift,getThe,throwThe,StateT.map,Functor.map,Pure.pure,
    Id.run,modify,modifyGet,modifyThe,MonadStateOf.modifyGet,StateT.modifyGet,MatrixState.liftWork]
  generalize houtput : Native.Scan.portable _ _ _ _ _ _ _ _ = output at *
  cases hw : (Matrix.work state.limits output.work).run state.stats with
  | mk result stats =>
    simp only [ExceptT.run] at hw
    cases result
    all_goals simp [hw,hstatus,StateT.bind,StateT.pure,StateT.map,ExceptT.bindCont,
      ExceptT.mk,ExceptT.pure,Pure.pure,Bind.bind,Functor.map,MonadState.get,MonadStateOf.get,
      StateT.get,MonadStateOf.modifyGet,StateT.modifyGet,modifyGet,Id.run]
    all_goals (try split) <;> try simp_all
    all_goals (try split) <;> try simp_all
    all_goals (try split) <;> try simp_all
    all_goals (try split) <;> try simp_all
    all_goals (try split) <;> try simp_all
    all_goals simp_all [StateT.bind,StateT.pure,StateT.map,ExceptT.bindCont,
      ExceptT.mk,ExceptT.pure,Pure.pure,Bind.bind,Functor.map,MonadState.get,MonadStateOf.get,
      StateT.get,MonadStateOf.modifyGet,StateT.modifyGet,modifyGet,Id.run]
    all_goals grind

set_option linter.unusedSimpArgs false in
private theorem scan_work_error (state : MatrixState.State) (output : Native.Scan.Result)
    (error : MatrixError) (stats : MatrixStats) (hphase : state.phase = .scan)
    (hgeometry : state.geometry) (hquanta : state.quanta ≠ 0)
    (houtput : Native.Scan.portable state.field.modulus state.slots state.nativePivots state.scan
      4096 (state.limits.work-state.stats.work) 0 false = output)
    (hwork : (Matrix.work state.limits output.work).run state.stats = (.error error,stats)) :
    outcome state = (.error error,stats) := by
  simp only [ExceptT.run] at hwork
  rw [outcome_run state hgeometry (by simp [hphase])]
  simp [MatrixState.step,MatrixState.takeScan,MatrixState.work,hphase,hquanta,houtput,hwork,
    ExceptT.run,ExceptT.mk,ExceptT.pure,ExceptT.bind,ExceptT.bindCont,ExceptT.lift,StateT.bind,
    StateT.get,StateT.set,StateT.pure,Bind.bind,MonadState.get,MonadStateOf.get,MonadStateOf.set,
    liftM,MonadLiftT.monadLift,MonadLift.monadLift,getThe,StateT.map,Functor.map,Pure.pure,
    Id.run,modify,modifyGet,modifyThe,MonadStateOf.modifyGet,StateT.modifyGet,MatrixState.liftWork]

private theorem scan_geometry (base : MatrixState.State) (data : Native.Scan.State)
    (quanta : Nat) (stats : MatrixStats) (hphase : base.phase = .scan)
    (hgeometry : base.geometry) (hdense : data.dense.size = base.scan.dense.size)
    (hquanta : quanta ≤ base.quanta) : (scanState base data quanta stats).geometry := by
  simp only [MatrixState.State.geometry,hphase] at hgeometry
  simp only [scanState,MatrixState.State.geometry]
  exact ⟨hdense.trans hgeometry.1,hgeometry.2.1,Nat.le_trans hquanta hgeometry.2.2⟩

private theorem scan_continue (state : MatrixState.State) (output : Native.Scan.Result)
    (stats : MatrixStats) (hphase : state.phase = .scan) (hgeometry : state.geometry)
    (hdense : output.state.dense.size = state.scan.dense.size) (hstatus : output.status = 0) :
    scanPending state output stats = outcome (scanState state output.state (state.quanta-1) stats) := by
  have geometry := scan_geometry state output.state (state.quanta-1) stats hphase hgeometry
    hdense (Nat.sub_le _ _)
  by_cases hlast : state.quanta = 1
  · have last := scan_zero (scanState state output.state (state.quanta-1) stats) rfl geometry
      (by simp [scanState,hlast])
    simpa [scanPending,hstatus,hlast,scanState] using last.symm
  · simp [scanPending,hstatus,hlast]

private theorem scan_self (base : MatrixState.State) (hphase : base.phase = .scan) :
    scanState base base.scan base.quanta base.stats = base := by
  unfold scanState
  rw [← hphase]

private def scanInverse (state : MatrixState.State) (data : Native.Scan.State) : Matrix.Work UInt64 :=
  if state.independent && MatrixState.isTarget state then pure 1
  else Matrix.inverse state.field state.field.barrett state.limits
    (Packed.read state.field.width data.dense (data.leading-1))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
private theorem scan_normalize (state : MatrixState.State) (output : Native.Scan.Result)
    (workStats : MatrixStats) (hphase : state.phase = .scan) (hgeometry : state.geometry)
    (hquanta : state.quanta ≠ 0)
    (houtput : Native.Scan.portable state.field.modulus state.slots state.nativePivots state.scan
      4096 (state.limits.work-state.stats.work) 0 false = output)
    (hwork : (Matrix.work state.limits output.work).run state.stats = (.ok (),workStats))
    (hstatus : output.status = 1) (hleading : output.state.leading ≠ 0) :
    outcome state = match (scanInverse state output.state).run
        { workStats with reductions := workStats.reductions+output.reductions } with
      | (.error error,stats) => (.error error,stats)
      | (.ok inverse,inverseStats) =>
        match (Matrix.work state.limits (output.state.last+1-(output.state.leading-1))).run inverseStats with
        | (.error error,stats) => (.error error,stats)
        | (.ok _,stats) => outcome (gatheredScan state output.state inverse stats) := by
  simp only [ExceptT.run] at hwork
  rw [outcome_run state hgeometry (by simp [hphase])]
  by_cases independent : state.independent = true ∧ MatrixState.isTarget state = true
  all_goals simp [MatrixState.step,MatrixState.takeScan,MatrixState.work,scanInverse,gatheredScan,
    hphase,hquanta,houtput,hwork,hstatus,hleading,independent,Native.Scan.transition,
    ExceptT.run,ExceptT.mk,ExceptT.pure,ExceptT.bind,ExceptT.bindCont,ExceptT.lift,StateT.bind,
    StateT.get,StateT.set,StateT.pure,Bind.bind,MonadState.get,MonadStateOf.get,MonadStateOf.set,
    MonadExcept.throw,MonadExceptOf.throw,liftM,MonadLiftT.monadLift,MonadLift.monadLift,getThe,
    throwThe,StateT.map,Functor.map,Pure.pure,Id.run,modify,modifyGet,modifyThe,
    MonadStateOf.modifyGet,StateT.modifyGet,MatrixState.liftWork]
  all_goals (try split) <;> try simp_all
  all_goals (try split) <;> try simp_all
  all_goals (try split) <;> try simp_all
  all_goals (try split) <;> try simp_all
  all_goals simp_all [StateT.bind,StateT.pure,StateT.map,ExceptT.bindCont,ExceptT.mk,
    ExceptT.pure,Pure.pure,Bind.bind,Functor.map,MonadState.get,MonadStateOf.get,StateT.get,
    MonadStateOf.modifyGet,StateT.modifyGet,modifyGet,Id.run]
  all_goals grind

private theorem normalization_geometry (state : MatrixState.State) (data : Native.Scan.State)
    (inverse : UInt64) (stats : MatrixStats) (hphase : state.phase = .scan)
    (hgeometry : state.geometry) (hdense : data.dense.size = state.columns*state.field.width.bytes)
    (hlast : data.last < max 1 state.columns) (hleading : data.leading ≤ state.columns)
    (hpositive : data.leading ≠ 0) : (gatheredScan state data inverse stats).geometry := by
  simp only [MatrixState.State.geometry,hphase] at hgeometry
  simp only [gatheredScan,MatrixState.State.geometry]
  refine ⟨hdense,hgeometry.2.1,?_,?_⟩ <;> omega

#print axioms normalization_geometry

#print axioms scan_normalize

#print axioms scan_work_error
#print axioms scan_continue
#print axioms scan_pending

#print axioms scan_complete_gather

#print axioms scan_complete_zero

end Hex.Groebner
