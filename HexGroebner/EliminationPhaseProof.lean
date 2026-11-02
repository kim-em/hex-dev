/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
import all HexGroebner.EliminationOutcome
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

#print axioms install_run
#print axioms zero_run

end Hex.Groebner
