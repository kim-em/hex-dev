/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebnerStateNative
public import HexGroebner.MatrixValidation
-- Inspect logical loop bodies only; states are created exclusively by start.
import all HexGroebner.MatrixState
import all Init.Data.Range.Basic
public import HexGroebner.ScanProof
public import HexGroebner.MatrixStateSchedule

public section

namespace Hex.Groebner.MatrixStateReplay

open MatrixState

/-- Literal replay of the Lean model of validation and exact prefix counters.
This phase is independent of the platform's deliberately opaque word size. -/
theorem validation_example :
    let field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
    let r : SparseRow := ⟨⟨#[0,0,0,0,2,0,0,0]⟩,⟨#[2,1]⟩⟩
    let t : SparseRow := ⟨⟨#[0,0,0,0,1,0,0,0]⟩,⟨#[4,1]⟩⟩
    let out := advance (start field {} 3 #[r] #[t] #[2,3] false) 2
    (out.phase == .validate && out.validation == 1 && out.stats.work == 3 &&
      out.stats.inputEntries == 2 && out.stats.packedBytes == 10) = true := by
  dsimp only
  rw [advance_spec]
  unfold advancePortable advanceWith start advancePhase step
  decide +kernel

/-- info: 'Hex.Groebner.MatrixStateReplay.validation_example' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms validation_example

/-- info: 'Hex.Groebner.Matrix.charge_run' does not depend on any axioms -/
#guard_msgs in #print axioms Matrix.charge_run
/-- info: 'Hex.Groebner.MatrixState.advance_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.advance_zero
/-- info: 'Hex.Groebner.MatrixState.next_done' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.next_done
/-- info: 'Hex.Groebner.MatrixState.advance_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.advance_done
/-- info: 'Hex.Groebner.MatrixState.finish_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.finish_done

/-- info: 'Hex.Groebner.MatrixState.validate_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.validate_ok
/-- info: 'Hex.Groebner.MatrixState.validate_error' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.validate_error

/-- info: 'Hex.Groebner.Matrix.validateFrom_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.validateFrom_zero
/-- info: 'Hex.Groebner.Native.Scan.untraced_events' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Native.Scan.untraced_events


/-- Instantiate the universal advance invariant on a concrete prime-field input,
checking that its public signature supports arbitrary bounded schedules. -/
theorem geometry_example (steps : Nat) :
    let field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
    let row : SparseRow := ⟨⟨#[0,0,0,0,2,0,0,0]⟩,⟨#[2,1]⟩⟩
    (advance (start field {} 3 #[] #[row] #[2] false) steps).geometry := by
  exact advance_geometry _ steps (start_geometry ..)

/-- info: 'Hex.Groebner.MatrixStateReplay.geometry_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms geometry_example
/-- info: 'Hex.Groebner.MatrixState.advance_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.advance_identity
/-- info: 'Hex.Groebner.MatrixState.workspace_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.workspace_ok
/-- info: 'Hex.Groebner.MatrixState.workspace_bytes_error' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.workspace_bytes_error
/-- info: 'Hex.Groebner.MatrixState.workspace_work_error' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.workspace_work_error
/-- info: 'Hex.Groebner.MatrixState.workspace_size_error' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.workspace_size_error

/-- Instantiate the completion theorem on a concrete input with symbolic
prefix length, quantum and provider; this checks its public signature. -/
theorem completion_example (steps quantum : Nat) (native : Bool) :
    let field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
    let row : SparseRow := ⟨⟨#[0,0,0,0,2,0,0,0]⟩,⟨#[2,1]⟩⟩
    let state := advance (start field {} 3 #[] #[row] #[2] false) steps
    let out := finishState quantum state native
    out.phase = .done ∧ out.result.isSome = true := by
  refine ⟨finishState_done _ quantum native ?_,finishState_result _ quantum native ?_⟩
  · exact (advance_valid _ steps (start_valid ..)).1
  · exact advance_valid _ steps (start_valid ..)

/-- info: 'Hex.Groebner.MatrixStateReplay.completion_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms completion_example
/-- info: 'Hex.Groebner.MatrixState.finishState_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.finishState_done
/-- info: 'Hex.Groebner.MatrixState.finishState_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.finishState_result

/-- Instantiate exact resumption on a concrete input with symbolic prefix and
quantum. The kernel checks the proof without evaluating the matrix algorithm. -/
theorem resumption_example (steps quantum : Nat) (native : Bool) :
    let field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
    let row : SparseRow := ⟨⟨#[0,0,0,0,2,0,0,0]⟩,⟨#[2,1]⟩⟩
    let initial := start field {} 3 #[] #[row] #[2] false
    finishWith quantum (advance initial steps) native = finishWith quantum initial native := by
  exact finishWith_resume _ steps quantum native (start_geometry ..)

/-- info: 'Hex.Groebner.MatrixStateReplay.resumption_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resumption_example
/-- info: 'Hex.Groebner.MatrixState.finishState_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.finishState_schedule

/-- Evaluate an actual terminal error and its exact counters in the kernel.
The explicit column limit fails before the platform-dependent workspace check. -/
theorem error_completion_example :
    let field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
    let initial := start field { columns := 2 } 3 #[] #[] #[] false
    finishWith 0 initial false = (.error (.exhausted .columns),{}) := by
  dsimp only
  unfold finishWith finishState State.allowance advancePortable advanceWith start advancePhase step
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

/-- info: 'Hex.Groebner.MatrixStateReplay.error_completion_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms error_completion_example
/-- Evaluate an exhausted validation with a nonzero charged prefix. The second
work charge fails after input entries and packed bytes have already been charged. -/
theorem charged_completion_example :
    let field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
    let r : SparseRow := ⟨⟨#[0,0,0,0,2,0,0,0]⟩,⟨#[2,1]⟩⟩
    let t : SparseRow := ⟨⟨#[0,0,0,0,1,0,0,0]⟩,⟨#[4,1]⟩⟩
    let initial := start field { work := 2 } 3 #[r] #[t] #[] false
    finishWith 0 initial false =
      (.error (.exhausted .work),{ work := 1,inputEntries := 2,packedBytes := 10 }) := by
  dsimp only
  unfold finishWith finishState State.allowance advancePortable advanceWith start advancePhase step
    liftWork Matrix.validate Matrix.work Matrix.charge
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

/-- info: 'Hex.Groebner.MatrixStateReplay.charged_completion_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms charged_completion_example
/-- info: 'Hex.Groebner.MatrixState.finishState_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.finishState_valid
/-- info: 'Hex.Groebner.MatrixState.advance_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.advance_one
/-- info: 'Hex.Groebner.MatrixState.finishWith_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.finishWith_next

end Hex.Groebner.MatrixStateReplay
