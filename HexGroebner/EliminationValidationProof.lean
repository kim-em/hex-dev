/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
import all HexGroebner.MatrixStateProof
import all HexGroebner.EliminationOutcome
public import HexGroebner.EliminationOutcome

public section

/-! Owning correspondence proofs inspect private continuation bodies. Public
State construction stays behind the executable API; do not expose unchecked
State builders from this module. -/

namespace Hex.Groebner

private noncomputable def validationTail (state : MatrixState.State)
    (result : Except MatrixError Unit × MatrixStats) :
    Except MatrixError (Echelon × Array RemainderRow) × MatrixStats :=
  match result with
  | (.error error,stats) => (.error error,stats)
  | (.ok _,stats) => outcome { state with
      phase := .workspace
      validation := max state.validation (state.reducers.size+state.targets.size)
      stats := stats }

private theorem validation_tail_step (state : MatrixState.State) (stats : MatrixStats)
    (result : Except MatrixError Unit × MatrixStats)
    (hcursor : state.validation < state.reducers.size+state.targets.size) :
    validationTail { state with validation := state.validation+1,stats } result =
      validationTail state result := by
  rcases result with ⟨result,finalStats⟩
  cases result <;> simp [validationTail,Nat.max_eq_right (Nat.le_of_lt hcursor),
    Nat.max_eq_right (show state.validation+1 ≤ state.reducers.size+state.targets.size by omega)]

private theorem validate_end (state : MatrixState.State)
    (hphase : state.phase = .validate)
    (hcursor : state.reducers.size+state.targets.size ≤ state.validation) :
    MatrixState.nextPortable state = { state with phase := .workspace } := by
  simp [MatrixState.nextPortable,MatrixState.advancePhase,MatrixState.step,hphase,hcursor,
    ExceptT.run,ExceptT.mk,ExceptT.bind,ExceptT.bindCont,ExceptT.lift,StateT.bind,StateT.get,
    StateT.set,Bind.bind,MonadState.get,MonadStateOf.get,MonadStateOf.set,
    liftM,MonadLiftT.monadLift,MonadLift.monadLift,getThe,StateT.map,
    Functor.map,Pure.pure,Id.run,
    show (MatrixState.Phase.validate == MatrixState.Phase.done) = false from rfl]

/-- Residual reference validation has the same completed outcome as the
continuation, including malformed inputs and every exhausted prefix. -/
private theorem validation_outcome (state : MatrixState.State) (hphase : state.phase = .validate) :
    outcome state = validationTail state
      ((Matrix.validateFrom state.field state.limits state.columns state.reducers state.targets
        state.validation).run state.stats) := by
  have geometry : state.geometry := by simp [MatrixState.State.geometry,hphase]
  have same := outcome_next state geometry
  by_cases hcursor : state.validation < state.reducers.size+state.targets.size
  · cases hrow : (Matrix.validate state.field state.limits state.columns state.validation
        (if state.validation < state.reducers.size then state.reducers[state.validation]!
          else state.targets[state.validation-state.reducers.size]!)).run state.stats with
    | mk result stats =>
      cases result with
      | error error =>
        rw [Matrix.validateFrom_error _ _ _ _ _ _ _ _ error hcursor hrow]
        rw [← MatrixState.next_spec,MatrixState.next_validate state stats (.error error)
          hphase hcursor hrow] at same
        simpa [validationTail,outcome,MatrixState.finish_done] using same.symm
      | ok value =>
        cases value
        rw [Matrix.validateFrom_ok _ _ _ _ _ _ _ _ hcursor hrow]
        rw [← MatrixState.next_spec,MatrixState.next_validate state stats (.ok ())
          hphase hcursor hrow] at same
        have rest := validation_outcome { state with validation := state.validation+1,stats }
          (by simpa using hphase)
        exact same.symm.trans (rest.trans (validation_tail_step state stats _ hcursor))
  · have hle := Nat.le_of_not_lt hcursor
    rw [Matrix.validateFrom_of_le _ _ _ _ _ _ hle]
    rw [validate_end state hphase hle] at same
    simpa [validationTail,Nat.max_eq_left hle,ExceptT.run,ExceptT.mk,ExceptT.pure,Pure.pure,StateT.pure,Id.run] using same.symm
termination_by state.reducers.size+state.targets.size-state.validation
decreasing_by simp_wf; omega

#print axioms validation_outcome

end Hex.Groebner
