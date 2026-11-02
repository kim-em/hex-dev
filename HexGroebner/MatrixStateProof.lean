/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
public import HexGroebner.MatrixState
public import HexGroebner.MatrixProof
public import HexGroebner.ScanProof
public import HexGroebner.GatherProof
public import Std.Do
meta import Std.Tactic.Do

public section

namespace Hex.Groebner.MatrixState

/-- Fixed field, allowances and input identity of a matrix continuation. -/
def State.identity (state : State) :=
  (state.field,state.limits,state.columns,state.reducers,state.targets,state.sugars,state.independent)

/-- All continuation contents apart from charged statistics. -/
def State.frame (state : State) := (state.contents,state.phase,state.validation,state.result)

open Std.Do in
@[spec] private theorem lift_frame_spec (initial : State) (action : Matrix.Work α) :
    Std.Do.Triple (m := Work) (ps := .except MatrixError (.arg State .pure)) (liftWork action)
      (fun (state : State) => ⌜state.frame = initial.frame⌝)
      (fun _ (state : State) => ⌜state.frame = initial.frame⌝,
        fun _ (state : State) => ⌜state.frame = initial.frame⌝,PUnit.unit) := by
  simp only [Std.Do.Triple.iff]
  intro state h
  cases heq : action.run state.stats with
  | mk result stats =>
    cases result <;> simpa [liftWork,ExceptT.run,ExceptT.mk,StateT.run,Id.run,Std.Do.WP.wp,
      State.frame,State.contents,show action state.stats = (_,stats) from heq] using h


set_option maxHeartbeats 2000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem step_identity_spec (initial : State) (native : Bool) :
    Std.Do.Triple (m := Work) (ps := .except MatrixError (.arg State .pure)) (step native)
      (fun (state : State) => ⌜state.identity = initial.identity⌝)
      (fun _ (state : State) => ⌜state.identity = initial.identity⌝,
        fun _ (state : State) => ⌜state.identity = initial.identity⌝,PUnit.unit) := by
  unfold step work install zeroRow completeRow isTarget takeDense takeScan takeGather
  mvcgen invariants
  · (fun _ (state : State) => ⌜state.identity = initial.identity⌝,
      fun _ (state : State) => ⌜state.identity = initial.identity⌝,PUnit.unit)
  · (fun _ (state : State) => ⌜state.identity = initial.identity⌝,
      fun _ (state : State) => ⌜state.identity = initial.identity⌝,PUnit.unit)
  all_goals simp_all +zetaDelta [State.identity,State.frame,State.contents]


private theorem phase_identity (state : State) (native : Bool) :
    (advancePhase state native).identity = state.identity := by
  by_cases hdone : state.phase == .done
  · simp [advancePhase,hdone]
  · have contract := step_identity_spec state native
    simp only [Std.Do.Triple.iff] at contract
    have h := contract state (by rfl)
    cases hr : (step native).run state with
    | mk result out =>
      change step native state = (result,out) at hr
      cases result <;>
        simpa [advancePhase,hdone,ExceptT.run,Std.Do.WP.wp,StateT.run,Id.run,Pure.pure,hr,State.identity] using h

/-- A phase preserves field, allowance and input identity on success and error. -/
theorem next_identity (state : State) : (next state).identity = state.identity :=
  phase_identity state true

/-- info: 'Hex.Groebner.MatrixState.next_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms next_identity


set_option linter.deprecated.syntax false in
open Std.Do in
private theorem advance_identity_spec (state : State) (steps : Nat) (native : Bool) :
    Std.Do.Triple (m := Id) (advanceWith state steps native) ⌜True⌝
      (PostCond.noThrow fun out => ⌜out.identity = state.identity⌝) := by
  unfold advanceWith
  dsimp only [Id.run]
  mvcgen invariants
  · ⟨fun ⟨_,out⟩ => ⌜out.identity = state.identity⌝,ExceptConds.false⟩
  all_goals simp_all [phase_identity]

/-- Every bounded native or portable advance retains the exact computation
identity, including states that terminate with an error inside the call. -/
theorem advance_identity (state : State) (steps : Nat) :
    (advance state steps).identity = state.identity := by
  rw [advance_spec]
  exact (advance_identity_spec state steps false) True.intro

/-- info: 'Hex.Groebner.MatrixState.advance_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms advance_identity


/-- Workspace geometry needed to bound the continuation's remaining phases.
Check/validation/workspace have not yet installed the dense buffers. -/
def State.geometry (state : State) : Prop :=
  let bytes := state.columns*state.field.width.bytes
  match state.phase with
  | .check | .validate | .workspace | .done => True
  | .input | .order => state.dense.size = bytes
  | .scan => state.scan.dense.size = bytes ∧ state.input < state.reducers.size+state.targets.size ∧
      state.quanta ≤ scanFuel state.columns
  | .gather => state.gather.dense.size = bytes ∧ state.input < state.reducers.size+state.targets.size ∧
      state.scan.last < state.columns ∧ state.quanta ≤ (state.columns+4095)/4096+1

/-- A new continuation has no active workspace yet. -/
theorem start_geometry (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) :
    (start field limits columns reducers targets sugars independent).geometry := by
  trivial

/-- Successful workspace setup establishes the active dense-buffer geometry. -/
theorem workspace_geometry (state : State) (packedStats stats : MatrixStats)
    (hphase : state.phase = .workspace)
    (hsize : state.columns*(state.field.width.bytes+4) < USize.size)
    (hpacked : (Matrix.packedBytes state.limits
      (state.columns*(state.field.width.bytes+4))).run state.stats = (.ok (),packedStats))
    (hwork : (Matrix.work state.limits
      (state.columns*(state.field.width.bytes+4))).run packedStats = (.ok (),stats)) :
    (next state).geometry := by
  have result := workspace_ok state packedStats stats hphase hsize hpacked hwork
  have identity := next_identity state
  simp only [State.identity,Prod.mk.injEq] at identity
  simp only [State.geometry,result.1,result.2.1,Matrix.zeros_size,identity.1,identity.2.2.1]


private theorem width_pos (field : PrimeField) : 0 < field.width.bytes := by
  cases field.width <;> decide

private theorem scan_geometry (field : PrimeField) (columns : Nat) (slots : ByteArray)
    (pivots : Array Native.Scan.Pivot) (initial : Native.Scan.State)
    (work : Nat) (native : Bool)
    (hsize : initial.dense.size = columns*field.width.bytes)
    (hstatus : (if native then Native.Scan.transition field.modulus slots pivots initial 4096 work 0 false
      else Native.Scan.portable field.modulus slots pivots initial 4096 work 0 false).status ≠ 4) :
    let out := if native then Native.Scan.transition field.modulus slots pivots initial 4096 work 0 false
      else Native.Scan.portable field.modulus slots pivots initial 4096 work 0 false
    out.state.dense.size = columns*field.width.bytes ∧
      out.state.last < max 1 columns ∧ out.state.leading ≤ columns := by
  cases native
  all_goals
    have bounds := Native.Scan.bounds_of_status field.modulus slots pivots initial 4096 work 0 false hstatus
    simp only [hsize,native_width,Nat.mul_div_cancel _ (width_pos field)] at bounds
    exact bounds

private theorem gather_size (field : PrimeField) (initial : Native.Gather.State)
    (stop entries bytes work : Nat) (factor : UInt64) (native : Bool) :
    (if native then Native.Gather.gather field.modulus initial stop 4096 entries bytes work factor
      else Native.Gather.portable field.modulus initial stop 4096 entries bytes work factor).state.dense.size =
      initial.dense.size := by
  cases native <;> exact Native.Gather.dense_size field.modulus initial stop 4096 entries bytes work factor


section


set_option maxHeartbeats 2000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem step_geometry_spec (initial : State) (native : Bool) (hgeometry : initial.geometry) :
    Std.Do.Triple (m := Work) (ps := .except MatrixError (.arg State .pure)) (step native)
      (fun (state : State) => ⌜state.frame = initial.frame⌝)
      (fun _ (state : State) => ⌜state.geometry⌝,
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
    · (fun _ (state : State) => ⌜state.geometry⌝,
        fun _ (_ : State) => ⌜True⌝,PUnit.unit)
    all_goals simp_all +zetaDelta [State.geometry,State.frame,State.contents,State.identity,
      Packed.size_set,Matrix.zeros_size,gather_size]
    all_goals try omega
    all_goals try grind [State.geometry,State.frame,State.contents,State.identity,scan_geometry,gather_size]
    all_goals
      simp only [Native.Scan.transition,ite_self] at *
      have bound := fun work => scan_geometry initial.field initial.columns initial.slots
        initial.nativePivots initial.scan work false
      simp only [Bool.false_eq_true,ite_false] at bound
      generalize hremaining : initial.limits.work - _ = remaining at *
      have hdense : initial.scan.dense.size = initial.columns*initial.field.width.bytes := by grind
      have hstatus : (Native.Scan.portable initial.field.modulus initial.slots initial.nativePivots
          initial.scan 4096 remaining 0 false).status ≠ 4 := by
        intro bad
        simp_all
      have actual := bound remaining hdense hstatus
      rcases actual with ⟨hbytes,hlast,hleading⟩
      clear bound
      try simp only [hbytes,true_and]
      all_goals omega


end


private theorem phase_geometry (state : State) (native : Bool) (hgeometry : state.geometry) :
    (advancePhase state native).geometry := by
  by_cases hdone : state.phase == .done
  · simpa [advancePhase,hdone] using hgeometry
  · have contract := step_geometry_spec state native hgeometry
    simp only [Std.Do.Triple.iff] at contract
    have h := contract state (by rfl)
    cases hr : (step native).run state with
    | mk result out =>
      change step native state = (result,out) at hr
      cases result
      · simp [advancePhase,hdone,ExceptT.run,hr,Pure.pure,Id.run,State.geometry]
      · simpa [advancePhase,hdone,ExceptT.run,Std.Do.WP.wp,StateT.run,Id.run,Pure.pure,hr] using h

/-- Each successful, suspended or failed phase preserves workspace geometry. -/
theorem next_geometry (state : State) (hgeometry : state.geometry) : (next state).geometry :=
  phase_geometry state true hgeometry

set_option linter.deprecated.syntax false in
open Std.Do in
private theorem advance_geometry_spec (state : State) (steps : Nat) (native : Bool)
    (hgeometry : state.geometry) :
    Std.Do.Triple (m := Id) (advanceWith state steps native) ⌜True⌝
      (PostCond.noThrow fun out => ⌜out.geometry⌝) := by
  unfold advanceWith
  dsimp only [Id.run]
  mvcgen invariants
  · ⟨fun ⟨_,out⟩ => ⌜out.geometry⌝,ExceptConds.false⟩
  all_goals simp_all [phase_geometry]

/-- Every bounded advance retains the exact active-workspace and cursor bounds. -/
theorem advance_geometry (state : State) (steps : Nat) (hgeometry : state.geometry) :
    (advance state steps).geometry := by
  rw [advance_spec]
  exact (advance_geometry_spec state steps false hgeometry) True.intro

/-- info: 'Hex.Groebner.MatrixState.next_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms next_geometry
/-- info: 'Hex.Groebner.MatrixState.advance_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms advance_geometry

end Hex.Groebner.MatrixState
