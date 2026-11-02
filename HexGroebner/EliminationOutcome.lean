/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
import all HexGroebner.MatrixStateProof
import all HexGroebner.MatrixStateFuel
import all HexGroebner.MatrixStateSchedule
import all HexGroebner.EliminationWorkProof
public import HexGroebner.MatrixStateSchedule
public import Std.Do
meta import Std.Tactic.Do

public section

/-! Owning correspondence proofs inspect private continuation bodies. Public
State construction stays behind the executable API; do not expose unchecked
State builders from this module. -/

namespace Hex.Groebner

private noncomputable def outcome (state : MatrixState.State) := MatrixState.finishWith 64 state false

/-- One phase preserves the completed result and every charged prefix counter. -/
private theorem outcome_next (state : MatrixState.State) (hgeometry : state.geometry) :
    outcome (MatrixState.nextPortable state) = outcome state := by
  rw [← MatrixState.next_spec]
  exact MatrixState.finishWith_next state 64 false hgeometry

/-- Successful atomic phases preserve geometry and the completed outcome. -/
private theorem outcome_ok (state out : MatrixState.State) (hgeometry : state.geometry)
    (hphase : state.phase ≠ .done)
    (hrun : (MatrixState.step false).run state = (.ok (),out)) :
    out.geometry ∧ outcome out = outcome state := by
  have hbool : ¬(state.phase == .done) = true :=
    fun h => hphase ((MatrixState.phase_done_beq _).1 h)
  change MatrixState.step false state = (.ok (),out) at hrun
  have update : MatrixState.nextPortable state = out := by
    simp [MatrixState.nextPortable,MatrixState.advancePhase,hbool,ExceptT.run,hrun,Pure.pure,Id.run]
  have geometry := MatrixState.next_geometry state hgeometry
  rw [MatrixState.next_spec,update] at geometry
  have same := outcome_next state hgeometry
  rw [update] at same
  exact ⟨geometry,same⟩

/-- A failed atomic phase has exactly the returned error and charged statistics. -/
private theorem outcome_error (state out : MatrixState.State) (error : MatrixError)
    (hgeometry : state.geometry) (hphase : state.phase ≠ .done)
    (hrun : (MatrixState.step false).run state = (.error error,out)) :
    outcome state = (.error error,out.stats) := by
  have hbool : ¬(state.phase == .done) = true :=
    fun h => hphase ((MatrixState.phase_done_beq _).1 h)
  change MatrixState.step false state = (.error error,out) at hrun
  have update : MatrixState.nextPortable state =
      { out with phase := .done,result := some (.error error) } := by
    simp [MatrixState.nextPortable,MatrixState.advancePhase,hbool,ExceptT.run,hrun,Pure.pure,Id.run]
  have same := outcome_next state hgeometry
  rw [update] at same
  simpa [outcome,MatrixState.finish_done] using same.symm

/-- Interpret one unfinished phase's exact run without discarding its error
state's statistics. Successful states continue with their completed outcome. -/
private theorem outcome_run (state : MatrixState.State) (hgeometry : state.geometry)
    (hphase : state.phase ≠ .done) :
    outcome state = match (MatrixState.step false).run state with
      | (.error error,out) => (.error error,out.stats)
      | (.ok _,out) => outcome out := by
  cases hr : (MatrixState.step false).run state with
  | mk result out =>
    cases result with
    | error error => exact outcome_error state out error hgeometry hphase hr
    | ok value =>
      cases value
      exact (outcome_ok state out hgeometry hphase hr).2.symm


#print axioms outcome_error

end Hex.Groebner
