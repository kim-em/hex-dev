/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
import all HexGroebner.MatrixStateProof
import all HexGroebner.MatrixStateFuel
public import HexGroebner.MatrixStateFuel
public import Std.Do
meta import Std.Tactic.Do

public section

/-! These owning proofs may inspect private continuation bodies. Keep public
state construction behind `start` and the executable transitions; do not expose
unchecked State builders from this proof module. -/

namespace Hex.Groebner.MatrixState

/-- Canonical completion by individual portable phases. The recursion is
well-founded on the proved phase count rather than an arbitrary fuel. -/
private noncomputable def complete (state : State) (hgeometry : state.geometry) : State :=
  if _hdone : state.phase == .done then state
  else complete (advancePhase state false) (phase_geometry state false hgeometry)
termination_by state.remaining
decreasing_by
  exact phase_remaining state false hgeometry (fun h => _hdone ((phase_done_beq _).2 h))

private theorem complete_done (state : State) (hgeometry : state.geometry)
    (hdone : state.phase = .done) : complete state hgeometry = state := by
  rw [complete]
  simp [hdone,show (Phase.done == Phase.done) = true from rfl]

private theorem complete_phase (state : State) (native : Bool) (hgeometry : state.geometry) :
    complete (advancePhase state native) (phase_geometry state native hgeometry) =
      complete state hgeometry := by
  cases native
  all_goals
    change complete (advancePhase state false) (phase_geometry state false hgeometry) =
      complete state hgeometry
    by_cases hdone : state.phase == .done
    · simp [advancePhase,hdone]
    · symm
      rw [complete]
      simp [hdone]

set_option maxHeartbeats 1000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem advance_complete_spec (state : State) (steps : Nat) (native : Bool)
    (hgeometry : state.geometry) :
    Std.Do.Triple (m := Id) (advanceWith state steps native) ⌜True⌝
      (PostCond.noThrow fun out => ⌜∃ h : out.geometry,complete out h = complete state hgeometry⌝) := by
  unfold advanceWith
  dsimp only [Id.run]
  mvcgen invariants
  · ⟨fun ⟨_,out⟩ => ⌜∃ h : out.geometry,complete out h = complete state hgeometry⌝,
      ExceptConds.false⟩
  all_goals try simp_all
  all_goals grind [phase_geometry,complete_phase]

private theorem advance_complete (state : State) (steps : Nat) (native : Bool)
    (hgeometry : state.geometry) :
    ∃ h : (if native then advance state steps else advancePortable state steps).geometry,
      complete (if native then advance state steps else advancePortable state steps) h =
        complete state hgeometry := by
  simp only [advance_spec]
  cases native <;> exact (advance_complete_spec state steps false hgeometry) True.intro

set_option maxHeartbeats 1000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem finish_complete_spec (state : State) (quantum : Nat) (native : Bool)
    (hgeometry : state.geometry) :
    Std.Do.Triple (m := Id) (finishState quantum state native) ⌜True⌝
      (PostCond.noThrow fun out => ⌜∃ h : out.geometry,complete out h = complete state hgeometry⌝) := by
  have batch : ∀ out (h : out.geometry),
      ∃ hout : (advancePortable out (max 1 quantum)).geometry,
        complete (advancePortable out (max 1 quantum)) hout = complete out h := by
    intro out h
    simpa only [advance_spec,ite_self] using advance_complete out (max 1 quantum) native h
  unfold finishState
  dsimp only [Id.run]
  mvcgen invariants
  · ⟨fun ⟨_,out⟩ => ⌜∃ h : out.geometry,complete out h = complete state hgeometry⌝,
      ExceptConds.false⟩
  all_goals try simp_all
  all_goals grind

/-- A single bounded advance is exactly one phase, including terminal states. -/
theorem advance_one (state : State) : advance state 1 = next state := by
  rw [advance_spec,next_spec]
  unfold advancePortable advanceWith
  have count : min 1 (max 1 (1048576 /
      (8*state.columns+2*(state.reducers.size+state.targets.size)+4224))) = 1 := by omega
  rw [count]
  simp only [Id.run,Std.Legacy.Range.forIn_eq_forIn_range']
  by_cases hdone : state.phase == .done
  all_goals simp [nextPortable,advancePhase,hdone,Pure.pure,Bind.bind,Id.run]

/-- Every bounded completion schedule produces the same entire final state,
including error outcomes, counters and workspace contents. -/
theorem finishState_schedule (state : State) (quantum₁ quantum₂ : Nat) (native₁ native₂ : Bool)
    (hgeometry : state.geometry) :
    finishState quantum₁ state native₁ = finishState quantum₂ state native₂ := by
  have left := (finish_complete_spec state quantum₁ native₁ hgeometry) True.intro
  have right := (finish_complete_spec state quantum₂ native₂ hgeometry) True.intro
  rcases left with ⟨hleft,left⟩
  rcases right with ⟨hright,right⟩
  rw [complete_done _ hleft (finishState_done state quantum₁ native₁ hgeometry)] at left
  rw [complete_done _ hright (finishState_done state quantum₂ native₂ hgeometry)] at right
  exact left.trans right.symm

/-- Completion quanta and provider choice preserve the exact result and every
charged resource counter in the Lean model. -/
theorem finishWith_schedule (state : State) (quantum₁ quantum₂ : Nat) (native₁ native₂ : Bool)
    (hgeometry : state.geometry) :
    finishWith quantum₁ state native₁ = finishWith quantum₂ state native₂ := by
  simp only [finishWith]
  rw [finishState_schedule state quantum₁ quantum₂ native₁ native₂ hgeometry]

/-- Suspending after any bounded prefix and completing later preserves the
entire final state, including exhausted-resource prefixes and terminal errors. -/
theorem finishState_resume (state : State) (steps quantum : Nat) (native : Bool)
    (hgeometry : state.geometry) :
    finishState quantum (advance state steps) native = finishState quantum state native := by
  have advanced : ∃ h : (advance state steps).geometry,
      complete (advance state steps) h = complete state hgeometry :=
    advance_complete state steps true hgeometry
  rcases advanced with ⟨hprefix,advanced⟩
  have left := (finish_complete_spec (advance state steps) quantum native hprefix) True.intro
  have right := (finish_complete_spec state quantum native hgeometry) True.intro
  rcases left with ⟨hleft,left⟩
  rcases right with ⟨hright,right⟩
  rw [complete_done _ hleft (finishState_done _ quantum native hprefix)] at left
  rw [complete_done _ hright (finishState_done state quantum native hgeometry)] at right
  exact left.trans (advanced.trans right.symm)

/-- Resumption preserves the complete result and exact resource counters. -/
theorem finishWith_resume (state : State) (steps quantum : Nat) (native : Bool)
    (hgeometry : state.geometry) :
    finishWith quantum (advance state steps) native = finishWith quantum state native := by
  simp only [finishWith]
  rw [finishState_resume state steps quantum native hgeometry]

/-- Resuming after a single phase preserves the entire completed state. -/
theorem finishState_next (state : State) (quantum : Nat) (native : Bool)
    (hgeometry : state.geometry) :
    finishState quantum (next state) native = finishState quantum state native := by
  rw [← advance_one]
  exact finishState_resume state 1 quantum native hgeometry

/-- One phase preserves the eventual result and exact resource counters. -/
theorem finishWith_next (state : State) (quantum : Nat) (native : Bool)
    (hgeometry : state.geometry) :
    finishWith quantum (next state) native = finishWith quantum state native := by
  simp only [finishWith]
  rw [finishState_next state quantum native hgeometry]

/-- info: 'Hex.Groebner.MatrixState.finishState_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finishState_schedule
/-- info: 'Hex.Groebner.MatrixState.finishState_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finishState_resume

end Hex.Groebner.MatrixState
