/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
import all HexGroebner.MatrixStateProof
public import HexGroebner.MatrixStateProof
public import Std.Do
meta import Std.Tactic.Do

public section

/-! These owning proofs may inspect private continuation bodies. Keep public
state construction behind `start` and the executable transitions; do not expose
unchecked State builders from this proof module. -/

namespace Hex.Groebner.MatrixState

/-- A decreasing phase count. Per-row weight covers input, scan and gather;
validation has its own remaining-row count before workspace setup. -/
def State.remaining (state : State) : Nat :=
  let rows := state.reducers.size+state.targets.size
  let gather := (state.columns+4095)/4096+1
  let weight := 2+scanFuel state.columns+gather
  match state.phase with
  | .check => 5+(rows-state.validation)+(rows-state.input)*weight
  | .validate => 4+(rows-state.validation)+(rows-state.input)*weight
  | .workspace => 3+(rows-state.input)*weight
  | .input => 2+(rows-state.input)*weight
  | .scan => 2+(rows-state.input-1)*weight+state.quanta+gather+1
  | .gather => 2+(rows-state.input-1)*weight+state.quanta
  | .order => 1
  | .done => 0

/-- A positive phase count characterizes unfinished continuations. -/
theorem remaining_pos (state : State) : 0 < state.remaining ↔ state.phase ≠ .done := by
  cases h : state.phase <;> simp [State.remaining,h] <;> omega

private theorem row_remaining (rows input weight : Nat) (h : input < rows) :
    (rows-input)*weight = (rows-input-1)*weight+weight := by
  rw [show rows-input = (rows-input-1)+1 from by omega,Nat.add_mul,Nat.one_mul]
  congr 1

set_option maxHeartbeats 2000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem step_remaining_spec (initial : State) (native : Bool)
    (hgeometry : initial.geometry) (hdone : initial.phase ≠ .done) :
    Std.Do.Triple (m := Work) (ps := .except MatrixError (.arg State .pure)) (step native)
      (fun (state : State) => ⌜state.frame = initial.frame⌝)
      (fun _ (state : State) => ⌜state.remaining < initial.remaining⌝,
        fun _ (_ : State) => ⌜True⌝,PUnit.unit) := by
  cases hphase : initial.phase
  all_goals
    unfold step work install zeroRow completeRow isTarget takeDense takeScan takeGather
    mvcgen invariants
    · (fun ⟨_,dense⟩ (state : State) =>
          ⌜dense.size = initial.columns*initial.field.width.bytes ∧
            state.identity = initial.identity ∧ state.input = initial.input ∧
            initial.input < initial.reducers.size+initial.targets.size⌝,
        fun _ (_ : State) => ⌜True⌝,PUnit.unit)
    · (fun _ (_ : State) => ⌜True⌝,
        fun _ (_ : State) => ⌜True⌝,PUnit.unit)
    all_goals simp_all +zetaDelta [State.remaining,State.geometry,State.frame,State.contents,
      State.identity,Packed.size_set]
    all_goals try omega
    all_goals try grind [State.remaining,State.geometry,State.frame,State.contents,State.identity]
    all_goals
      have hinput : initial.input < initial.reducers.size+initial.targets.size := by grind [State.geometry]
      have row := row_remaining (initial.reducers.size+initial.targets.size) initial.input
        (2+scanFuel initial.columns+((initial.columns+4095)/4096+1)) hinput
      try simp only [Nat.sub_add_eq] at *
      try omega
    all_goals
      simp only [Native.Scan.transition,ite_self] at *
      generalize hremaining : initial.limits.work - _ = remaining at *
      have hdense : initial.scan.dense.size = initial.columns*initial.field.width.bytes := by grind
      have hstatus : (Native.Scan.portable initial.field.modulus initial.slots initial.nativePivots
          initial.scan 4096 remaining 0 false).status ≠ 4 := by
        intro bad
        simp_all
      have actual := scan_bounds initial remaining hdense hstatus
      rcases actual with ⟨hbytes,hlast,hleading⟩
      omega

private theorem phase_remaining (state : State) (native : Bool)
    (hgeometry : state.geometry) (hdone : state.phase ≠ .done) :
    (advancePhase state native).remaining < state.remaining := by
  have hbool : ¬(state.phase == .done) = true := by
    cases h : state.phase <;> simp_all <;> decide
  have contract := step_remaining_spec state native hgeometry hdone
  simp only [Std.Do.Triple.iff] at contract
  have h := contract state (by rfl)
  cases hr : (step native).run state with
  | mk result out =>
    change step native state = (result,out) at hr
    cases result
    · simpa [advancePhase,hbool,ExceptT.run,hr,Pure.pure,Id.run,State.remaining]
        using (remaining_pos state).2 hdone
    · simpa [advancePhase,hbool,ExceptT.run,Std.Do.WP.wp,StateT.run,Id.run,Pure.pure,hr] using h

/-- Every unfinished phase strictly decreases the remaining phase count,
including phase transitions that finish with an error. -/
theorem next_remaining (state : State) (hgeometry : state.geometry) (hdone : state.phase ≠ .done) :
    (next state).remaining < state.remaining :=
  phase_remaining state true hgeometry hdone

private theorem phase_remaining_le (state : State) (native : Bool) (hgeometry : state.geometry) :
    (advancePhase state native).remaining ≤ state.remaining := by
  by_cases hdone : state.phase = .done
  · simp [advancePhase,hdone,show (Phase.done == Phase.done) = true from rfl,Pure.pure,Id.run]
  · exact Nat.le_of_lt (phase_remaining state native hgeometry hdone)

/-- info: 'Hex.Groebner.MatrixState.next_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms next_remaining

private theorem phase_done_beq (phase : Phase) : (phase == .done) = true ↔ phase = .done := by
  cases phase <;> constructor <;> intro h <;> cases h <;> rfl

set_option maxHeartbeats 1000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem advance_remaining_spec (state : State) (steps : Nat) (native : Bool)
    (hgeometry : state.geometry) (hdone : state.phase ≠ .done) (hsteps : 0 < steps) :
    Std.Do.Triple (m := Id) (advanceWith state steps native) ⌜True⌝
      (PostCond.noThrow fun out => ⌜out.geometry ∧ out.remaining < state.remaining⌝) := by
  have hcount : 0 < min steps
      (max 1 (1048576/(8*state.columns+2*(state.reducers.size+state.targets.size)+4224))) := by omega
  unfold advanceWith
  dsimp only [Id.run]
  mvcgen invariants
  · ⟨fun ⟨cursor,out⟩ => ⌜out.geometry ∧ out.remaining ≤ state.remaining ∧
        (cursor.prefix = [] → out = state) ∧
        (cursor.prefix ≠ [] → out.remaining < state.remaining)⌝,ExceptConds.false⟩
  all_goals try simp_all [phase_done_beq]
  all_goals try grind [phase_geometry,phase_remaining,phase_remaining_le]

/-- A positive bounded call strictly decreases the remaining phase count when
started unfinished. The native provider has the same scalar definition. -/
theorem advance_remaining (state : State) (steps : Nat) (hgeometry : state.geometry)
    (hdone : state.phase ≠ .done) (hsteps : 0 < steps) :
    (advance state steps).remaining < state.remaining := by
  rw [advance_spec]
  exact ((advance_remaining_spec state steps false hgeometry hdone hsteps) True.intro).2

/-- info: 'Hex.Groebner.MatrixState.advance_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms advance_remaining

/-- Every geometrically valid continuation fits its own shape allowance,
including a continuation suspended partway through a row. -/
theorem remaining_lt_allowance (state : State) (hgeometry : state.geometry) :
    state.remaining < state.allowance := by
  let rows := state.reducers.size+state.targets.size
  let weight := 2+scanFuel state.columns+((state.columns+4095)/4096+1)
  have hrows := Nat.sub_le rows state.validation
  have hinput := Nat.mul_le_mul_right weight (Nat.sub_le rows state.input)
  have hscan := Nat.mul_le_mul_right weight
    (Nat.le_trans (Nat.sub_le (rows-state.input) 1) (Nat.sub_le rows state.input))
  dsimp only [rows,weight] at *
  cases hphase : state.phase
  all_goals
    simp only [State.remaining,State.allowance,State.geometry,hphase] at *
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one] at *
    omega

/-- info: 'Hex.Groebner.MatrixState.remaining_lt_allowance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms remaining_lt_allowance

/-- The outer allowance strictly exceeds a new computation's phase count. -/
theorem start_remaining (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) :
    (start field limits columns reducers targets sugars independent).remaining <
      (start field limits columns reducers targets sugars independent).allowance :=
  remaining_lt_allowance _ (start_geometry ..)

set_option maxHeartbeats 1000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem finish_state_spec (state : State) (quantum : Nat) (native : Bool)
    (hgeometry : state.geometry) :
    Std.Do.Triple (m := Id) (finishState quantum state native) ⌜True⌝
      (PostCond.noThrow fun out => ⌜out.geometry ∧ out.phase = .done⌝) := by
  have bound := remaining_lt_allowance state hgeometry
  have geometry : ∀ out : State, out.geometry →
      (advancePortable out (max 1 quantum)).geometry := by
    intro out h
    simpa only [advance_spec] using advance_geometry out (max 1 quantum) h
  have decreases : ∀ out : State, out.geometry → out.phase ≠ .done →
      (advancePortable out (max 1 quantum)).remaining < out.remaining := by
    intro out h unfinished
    simpa only [advance_spec] using advance_remaining out (max 1 quantum) h unfinished (by omega)
  unfold finishState
  dsimp only [Id.run]
  mvcgen invariants
  · ⟨fun ⟨cursor,out⟩ => ⌜out.geometry ∧
        (out.phase = .done ∨ out.remaining+cursor.prefix.length ≤ state.remaining)⌝,
      ExceptConds.false⟩
  all_goals try simp_all [phase_done_beq]
  case vc2.step.isFalse =>
    rename_i pref cur suff out hlist hdone hinv
    apply Or.inr
    have strict := decreases out hinv.1 hdone
    omega
  case vc4.post.success =>
    rename_i out hinv
    rcases hinv with ⟨_,hdone | hremaining⟩
    · exact hdone
    · omega

/-- Every valid continuation finishes within its shape allowance, for every
requested quantum and either provider, including resumed scan and gather states. -/
theorem finishState_done (state : State) (quantum : Nat) (native : Bool)
    (hgeometry : state.geometry) : (finishState quantum state native).phase = .done :=
  ((finish_state_spec state quantum native hgeometry) True.intro).2

/-- info: 'Hex.Groebner.MatrixState.finishState_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finishState_done

/-- Terminal continuations carry a completed success or error result. -/
def State.closed (state : State) : Prop := state.phase = .done → state.result.isSome = true

/-- Workspace bounds and the terminal-result invariant needed for completion. -/
@[expose] def State.valid (state : State) : Prop := state.geometry ∧ state.closed

/-- New computations have no terminal-result obligation yet. -/
theorem start_closed (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) :
    (start field limits columns reducers targets sugars independent).closed := by
  simp [State.closed,start]

set_option maxHeartbeats 2000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem step_closed_spec (initial : State) (native : Bool) (hclosed : initial.closed) :
    Std.Do.Triple (m := Work) (ps := .except MatrixError (.arg State .pure)) (step native)
      (fun (state : State) => ⌜state.frame = initial.frame⌝)
      (fun _ (state : State) => ⌜state.closed⌝,
        fun _ (_ : State) => ⌜True⌝,PUnit.unit) := by
  cases hphase : initial.phase
  all_goals
    unfold step work install zeroRow completeRow isTarget takeDense takeScan takeGather
    mvcgen invariants
    · (fun _ (state : State) => ⌜state.phase = .input⌝,
        fun _ (_ : State) => ⌜True⌝,PUnit.unit)
    · (fun _ (state : State) => ⌜state.phase = .order⌝,
        fun _ (_ : State) => ⌜True⌝,PUnit.unit)
    all_goals simp_all +zetaDelta [State.closed,State.frame,State.contents]
    all_goals grind [State.closed,State.frame,State.contents]

private theorem phase_closed (state : State) (native : Bool) (hclosed : state.closed) :
    (advancePhase state native).closed := by
  by_cases hdone : state.phase == .done
  · simpa [advancePhase,hdone] using hclosed
  · have contract := step_closed_spec state native hclosed
    simp only [Std.Do.Triple.iff] at contract
    have h := contract state (by rfl)
    cases hr : (step native).run state with
    | mk result out =>
      change step native state = (result,out) at hr
      cases result
      · simp [advancePhase,hdone,ExceptT.run,hr,Pure.pure,Id.run,State.closed]
      · simpa [advancePhase,hdone,ExceptT.run,Std.Do.WP.wp,StateT.run,Id.run,Pure.pure,hr] using h

/-- A phase retains a completed result whenever it is terminal. -/
theorem next_closed (state : State) (hclosed : state.closed) : (next state).closed :=
  phase_closed state true hclosed

set_option linter.deprecated.syntax false in
open Std.Do in
private theorem advance_closed_spec (state : State) (steps : Nat) (native : Bool)
    (hclosed : state.closed) :
    Std.Do.Triple (m := Id) (advanceWith state steps native) ⌜True⌝
      (PostCond.noThrow fun out => ⌜out.closed⌝) := by
  unfold advanceWith
  dsimp only [Id.run]
  mvcgen invariants
  · ⟨fun ⟨_,out⟩ => ⌜out.closed⌝,ExceptConds.false⟩
  all_goals simp_all [phase_closed]

/-- Bounded schedules preserve terminal success and error results. -/
theorem advance_closed (state : State) (steps : Nat) (hclosed : state.closed) :
    (advance state steps).closed := by
  rw [advance_spec]
  exact (advance_closed_spec state steps false hclosed) True.intro

set_option linter.deprecated.syntax false in
open Std.Do in
private theorem finish_closed_spec (state : State) (quantum : Nat) (native : Bool)
    (hclosed : state.closed) :
    Std.Do.Triple (m := Id) (finishState quantum state native) ⌜True⌝
      (PostCond.noThrow fun out => ⌜out.closed⌝) := by
  have closed : ∀ out : State, out.closed → (advancePortable out (max 1 quantum)).closed := by
    intro out h
    simpa only [advance_spec] using advance_closed out (max 1 quantum) h
  unfold finishState
  dsimp only [Id.run]
  mvcgen invariants
  · ⟨fun ⟨_,out⟩ => ⌜out.closed⌝,ExceptConds.false⟩
  all_goals simp_all

/-- Completion preserves the active-workspace bounds. -/
theorem finishState_geometry (state : State) (quantum : Nat) (native : Bool)
    (hgeometry : state.geometry) : (finishState quantum state native).geometry :=
  ((finish_state_spec state quantum native hgeometry) True.intro).1

/-- Terminal results survive completion, including already completed inputs. -/
theorem finishState_closed (state : State) (quantum : Nat) (native : Bool)
    (hclosed : state.closed) : (finishState quantum state native).closed :=
  (finish_closed_spec state quantum native hclosed) True.intro

/-- New continuations satisfy both completion invariants. -/
theorem start_valid (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) :
    (start field limits columns reducers targets sugars independent).valid :=
  ⟨start_geometry ..,start_closed field limits columns reducers targets sugars independent⟩

/-- One phase preserves both completion invariants. -/
theorem next_valid (state : State) (hvalid : state.valid) : (next state).valid :=
  ⟨next_geometry state hvalid.1,next_closed state hvalid.2⟩

/-- Every bounded schedule preserves both completion invariants. -/
theorem advance_valid (state : State) (steps : Nat) (hvalid : state.valid) :
    (advance state steps).valid :=
  ⟨advance_geometry state steps hvalid.1,advance_closed state steps hvalid.2⟩

/-- Completing a valid continuation retains both invariants. -/
theorem finishState_valid (state : State) (quantum : Nat) (native : Bool)
    (hvalid : state.valid) : (finishState quantum state native).valid :=
  ⟨finishState_geometry state quantum native hvalid.1,finishState_closed state quantum native hvalid.2⟩

/-- Completion always has a stored success or error, for any valid resumed state
whose terminal states have results. The empty-result fallback is unreachable.
Per-row quantum exhaustion can still be a stored `rowUpdate` error. -/
theorem finishState_result (state : State) (quantum : Nat) (native : Bool)
    (hvalid : state.valid) : (finishState quantum state native).result.isSome = true :=
  finishState_closed state quantum native hvalid.2
    (finishState_done state quantum native hvalid.1)

/-- info: 'Hex.Groebner.MatrixState.finishState_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finishState_result
/-- info: 'Hex.Groebner.MatrixState.advance_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms advance_closed

/-- info: 'Hex.Groebner.MatrixState.remaining_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms remaining_pos
/-- info: 'Hex.Groebner.MatrixState.start_remaining' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms start_remaining

end Hex.Groebner.MatrixState
