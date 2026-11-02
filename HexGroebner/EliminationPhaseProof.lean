/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
import all HexGroebner.EliminationOutcome
import all HexGroebner.MatrixStateProof
public import HexGroebner.EliminationOutcome

public section

/-! These owning phase proofs inspect private continuation bodies. Do not
expose public unchecked State builders from this module. -/

namespace Hex.Groebner

private theorem install_run (state : MatrixState.State) (row : SparseRow)
    (column : Nat) (inverse : UInt64) (sugar : Nat) :
    (MatrixState.install row column inverse sugar).run state = (.ok (),
      if state.independent && MatrixState.isTarget state then
        { state with
          remainders := state.remainders.push ⟨row,none,sugar⟩
          input := state.input+1
          phase := .input
          stats.processedRows := state.stats.processedRows+1 }
      else
        { state with
          slots := Packed.set .u32 state.slots column (state.pivots.size+1).toUInt64
          pivots := state.pivots.push ⟨row,MatrixState.isTarget state,none,inverse,sugar⟩
          nativePivots := state.nativePivots.push ⟨row.columns,row.coefficients,sugar⟩
          rank := state.rank + if MatrixState.isTarget state then 0 else 1
          input := state.input+1
          phase := .input
          stats.processedRows := state.stats.processedRows+1 }) := by
  by_cases h : state.independent && MatrixState.isTarget state
  all_goals simp [MatrixState.install,MatrixState.completeRow,h,ExceptT.run,ExceptT.mk,
    ExceptT.bind,ExceptT.bindCont,ExceptT.lift,StateT.bind,StateT.get,StateT.set,Bind.bind,MonadState.get,MonadStateOf.get,MonadStateOf.set,liftM,
    MonadLiftT.monadLift,MonadLift.monadLift,getThe,StateT.map,Functor.map,Pure.pure,modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet]

private theorem zero_run (state : MatrixState.State) :
    MatrixState.zeroRow.run state = (.ok (),
      { state with
        remainders := if state.independent && MatrixState.isTarget state then
          state.remainders.push ⟨{},none,state.sugar⟩ else state.remainders
        input := state.input+1
        phase := .input
        stats.zeroRows := state.stats.zeroRows+1
        stats.processedRows := state.stats.processedRows+1 }) := by
  simp [MatrixState.zeroRow,MatrixState.completeRow,ExceptT.run,ExceptT.mk,ExceptT.bind,
    ExceptT.bindCont,ExceptT.lift,StateT.bind,Bind.bind,MonadLiftT.monadLift,MonadLift.monadLift,StateT.map,Functor.map,Pure.pure,modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet]

private theorem check_run (state : MatrixState.State) (hphase : state.phase = .check) :
    (MatrixState.step false).run state =
      if state.columns > 4294967295 || state.reducers.size+state.targets.size > 4294967295 then
        (.error .dimensions,state)
      else if state.columns > state.limits.columns then (.error (.exhausted .columns),state)
      else if state.reducers.size+state.targets.size > state.limits.rows then
        (.error (.exhausted .rows),state)
      else if !state.sugars.isEmpty && state.sugars.size != state.reducers.size+state.targets.size then
        (.error .dimensions,state)
      else (.ok (),{ state with phase := .validate }) := by
  simp [MatrixState.step,hphase,ExceptT.run,ExceptT.mk,ExceptT.bind,ExceptT.bindCont,
    ExceptT.lift,StateT.bind,StateT.get,StateT.set,StateT.pure,Bind.bind,MonadState.get,
    MonadStateOf.get,MonadStateOf.set,MonadExcept.throw,MonadExceptOf.throw,liftM,
    MonadLiftT.monadLift,MonadLift.monadLift,getThe,throwThe,StateT.map,Functor.map,Pure.pure,
    Id.run]
  all_goals (try split) <;> try simp_all
  all_goals (try split) <;> try simp_all
  all_goals (try split) <;> try simp_all
  all_goals (try split) <;> try simp_all
  all_goals rfl


private theorem check_outcome (state : MatrixState.State) (hphase : state.phase = .check) :
    outcome state =
      if state.columns > 4294967295 || state.reducers.size+state.targets.size > 4294967295 then
        (.error .dimensions,state.stats)
      else if state.columns > state.limits.columns then (.error (.exhausted .columns),state.stats)
      else if state.reducers.size+state.targets.size > state.limits.rows then
        (.error (.exhausted .rows),state.stats)
      else if !state.sugars.isEmpty && state.sugars.size != state.reducers.size+state.targets.size then
        (.error .dimensions,state.stats)
      else outcome { state with phase := .validate } := by
  rw [outcome_run state (by simp [MatrixState.State.geometry,hphase]) (by simp [hphase]),
    check_run state hphase]
  split <;> simp_all
  all_goals split <;> simp_all
  all_goals split <;> simp_all
  all_goals split <;> simp_all

  all_goals split <;> simp_all

private noncomputable def workspaceTail (state : MatrixState.State)
    (result : Except MatrixError Unit × MatrixStats) :
    Except MatrixError (Echelon × Array RemainderRow) × MatrixStats :=
  match result with
  | (.error error,stats) => (.error error,stats)
  | (.ok _,stats) => outcome { state with
      phase := .input
      dense := Matrix.zeros (state.columns*state.field.width.bytes)
      slots := Matrix.zeros (state.columns*4)
      stats := stats }

private theorem workspace_outcome (state : MatrixState.State) (hphase : state.phase = .workspace) :
    let bytes := state.columns*(state.field.width.bytes+4)
    outcome state = if bytes ≥ USize.size then (.error .dimensions,state.stats) else
      workspaceTail state ((do
        Matrix.packedBytes state.limits bytes
        Matrix.work state.limits bytes).run state.stats) := by
  dsimp only
  have geometry : state.geometry := by simp [MatrixState.State.geometry,hphase]
  have same := outcome_next state geometry
  rw [← MatrixState.next_spec] at same
  by_cases hsize : state.columns*(state.field.width.bytes+4) < USize.size
  · simp only [show ¬state.columns*(state.field.width.bytes+4) ≥ USize.size by omega,ite_false]
    cases hp : (Matrix.packedBytes state.limits
        (state.columns*(state.field.width.bytes+4))).run state.stats with
    | mk result packedStats =>
      cases result with
      | error error =>
        rw [MatrixState.next_workspace_bytes state packedStats error hphase hsize hp] at same
        simp only [ExceptT.run] at hp
        simpa [workspaceTail,outcome,MatrixState.finish_done,ExceptT.run,ExceptT.mk,ExceptT.bind,
          ExceptT.bindCont,StateT.bind,StateT.pure,Bind.bind,Pure.pure,hp] using same.symm
      | ok value =>
        cases value
        cases hw : (Matrix.work state.limits
            (state.columns*(state.field.width.bytes+4))).run packedStats with
        | mk result stats =>
          cases result with
          | error error =>
            rw [MatrixState.next_workspace state packedStats stats (.error error) hphase hsize hp hw] at same
            simp only [ExceptT.run] at hp hw
            simpa [workspaceTail,outcome,MatrixState.finish_done,ExceptT.run,ExceptT.mk,ExceptT.bind,
              ExceptT.bindCont,StateT.bind,StateT.pure,Bind.bind,Pure.pure,hp,hw] using same.symm
          | ok value =>
            cases value
            rw [MatrixState.next_workspace state packedStats stats (.ok ()) hphase hsize hp hw] at same
            simp only [ExceptT.run] at hp hw
            simpa [workspaceTail,ExceptT.run,ExceptT.mk,ExceptT.bind,ExceptT.bindCont,
              StateT.bind,StateT.pure,Bind.bind,Pure.pure,hp,hw] using same.symm
  · have bad := Nat.le_of_not_lt hsize
    simp only [bad,ite_true]
    rw [MatrixState.next_workspace_size state hphase bad] at same
    simpa [outcome,MatrixState.finish_done] using same.symm

#print axioms workspace_outcome

#print axioms install_run
#print axioms zero_run

end Hex.Groebner
