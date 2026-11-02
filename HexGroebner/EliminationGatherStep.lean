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

/-! Owning gather correspondence proofs may inspect private phase bodies.
Do not expose public unchecked State builders from this module. -/

namespace Hex.Groebner

private noncomputable def gatherState (base : MatrixState.State) (data : Native.Gather.State)
    (quanta : Nat) (stats : MatrixStats) : MatrixState.State :=
  { base with phase := .gather,gather := data,quanta,stats }

private noncomputable def gatheredState (base : MatrixState.State) (row : SparseRow)
    (dense : ByteArray) (quanta : Nat) (stats : MatrixStats) : MatrixState.State :=
  ((MatrixState.install row base.leading base.inverse base.sugar).run
    { base with dense,gather := ⟨{},{},{},0⟩,quanta,stats }).2

private theorem gather_zero (state : MatrixState.State) (hphase : state.phase = .gather)
    (hgeometry : state.geometry) (hquanta : state.quanta = 0) :
    outcome state = (.error .rowUpdate,state.stats) := by
  apply outcome_error state state .rowUpdate hgeometry (by simp [hphase])
  simp [MatrixState.step,hphase,hquanta,ExceptT.run,ExceptT.mk,ExceptT.bind,ExceptT.bindCont,
    ExceptT.lift,StateT.bind,StateT.get,StateT.set,StateT.pure,Bind.bind,MonadState.get,
    MonadStateOf.get,MonadStateOf.set,MonadExcept.throw,MonadExceptOf.throw,liftM,
    MonadLiftT.monadLift,MonadLift.monadLift,getThe,throwThe,StateT.map,Functor.map,Pure.pure,
    Id.run]

private noncomputable def gatherTail (state : MatrixState.State) (output : Native.Gather.Result)
    (stats : MatrixStats) : Except MatrixError (Echelon × Array RemainderRow) × MatrixStats :=
  if output.status == 2 then (.error (.exhausted .outputEntries),stats)
  else if output.status == 3 then (.error (.exhausted .packedBytes),stats)
  else if output.status == 4 then (.error (.exhausted .work),stats)
  else if output.status == 5 then (.error .dimensions,stats)
  else if output.status != 0 && output.status != 1 then (.error .rowUpdate,stats)
  else if output.status == 0 && state.quanta == 1 then (.error .rowUpdate,stats)
  else if output.status == 1 then
    outcome (gatheredState state ⟨output.state.columns,output.state.coefficients⟩
      output.state.dense (state.quanta-1) stats)
  else outcome (gatherState state output.state (state.quanta-1) stats)

private def gatherCharges (state : MatrixState.State) (output : Native.Gather.Result) : Matrix.Work Unit := do
  Matrix.charge .outputEntries output.entries state.limits.outputEntries
    (·.outputEntries) fun stats n => { stats with outputEntries := n }
  Matrix.packedBytes state.limits output.bytes
  Matrix.work state.limits output.work

-- Shared transformer normalization rules cover both successful and failed charges.
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
private theorem gather_outcome (state : MatrixState.State) (hphase : state.phase = .gather)
    (hgeometry : state.geometry) (hquanta : state.quanta ≠ 0) :
    let output := Native.Gather.portable state.field.modulus state.gather (state.scan.last+1) 4096
      (state.limits.outputEntries-state.stats.outputEntries)
      (state.limits.packedBytes-state.stats.packedBytes)
      (state.limits.work-state.stats.work) state.inverse
    outcome state = match (gatherCharges state output).run state.stats with
      | (.error error,stats) => (.error error,stats)
      | (.ok _,stats) => gatherTail state output stats := by
  dsimp only
  have installFormula := fun state row column inverse sugar => install_run state row column inverse sugar
  simp only [ExceptT.run] at installFormula
  rw [outcome_run state hgeometry (by simp [hphase])]
  unfold MatrixState.step MatrixState.takeGather MatrixState.work gatherCharges
  simp only [hphase]
  simp [hphase,hquanta,gatherTail,gatherState,gatheredState,ExceptT.run,ExceptT.mk,ExceptT.pure,ExceptT.bind,
    ExceptT.bindCont,ExceptT.lift,StateT.bind,StateT.get,StateT.set,StateT.pure,Bind.bind,
    MonadState.get,MonadStateOf.get,MonadStateOf.set,MonadExcept.throw,MonadExceptOf.throw,
    liftM,MonadLiftT.monadLift,MonadLift.monadLift,getThe,throwThe,StateT.map,Functor.map,
    Pure.pure,Id.run,modify,modifyGet,modifyThe,MonadStateOf.modifyGet,StateT.modifyGet,
    MatrixState.liftWork]
  generalize houtput : Native.Gather.portable _ _ _ _ _ _ _ _ = output at *
  cases he : (Matrix.charge .outputEntries output.entries state.limits.outputEntries
      (·.outputEntries) fun stats n => { stats with outputEntries := n }).run state.stats with
  | mk entries entriesStats =>
    simp only [ExceptT.run] at he
    cases entries
    all_goals simp [he,hphase,hquanta,StateT.bind,StateT.pure,StateT.map,ExceptT.bindCont,
      ExceptT.mk,ExceptT.pure,Pure.pure,Bind.bind,Functor.map,MonadState.get,MonadStateOf.get,
      StateT.get,MonadStateOf.modifyGet,StateT.modifyGet,modifyGet,Id.run,houtput]
    all_goals
      cases hb : (Matrix.packedBytes state.limits output.bytes).run entriesStats with
      | mk bytes bytesStats =>
        simp only [ExceptT.run] at hb
        cases bytes
        all_goals simp [hb,hphase,hquanta,StateT.bind,StateT.pure,StateT.map,ExceptT.bindCont,
          ExceptT.mk,ExceptT.pure,Pure.pure,Bind.bind,Functor.map,MonadState.get,MonadStateOf.get,
          StateT.get,MonadStateOf.modifyGet,StateT.modifyGet,modifyGet,Id.run,houtput]
        all_goals
          cases hw : (Matrix.work state.limits output.work).run bytesStats with
          | mk work stats =>
            simp only [ExceptT.run] at hw
            cases work
            all_goals simp [hw,hphase,hquanta,StateT.bind,StateT.pure,StateT.map,ExceptT.bindCont,
              ExceptT.mk,ExceptT.pure,Pure.pure,Bind.bind,Functor.map,MonadState.get,MonadStateOf.get,
              StateT.get,MonadStateOf.modifyGet,StateT.modifyGet,modifyGet,Id.run,houtput]
            all_goals (try split) <;> try simp_all
            all_goals (try split) <;> try simp_all
            all_goals (try split) <;> try simp_all
            all_goals (try split) <;> try simp_all
            all_goals (try split) <;> try simp_all
            all_goals (try split) <;> try simp_all
            all_goals (try split) <;> try simp_all
            all_goals (try split) <;> try simp_all
            all_goals simp_all [StateT.bind,StateT.pure,StateT.map,ExceptT.bindCont,
              ExceptT.mk,ExceptT.pure,Pure.pure,Bind.bind,Functor.map,MonadState.get,MonadStateOf.get,
              StateT.get,MonadStateOf.modifyGet,StateT.modifyGet,modifyGet,Id.run,installFormula]
            all_goals grind



#print axioms gather_outcome
#print axioms gather_zero

end Hex.Groebner
