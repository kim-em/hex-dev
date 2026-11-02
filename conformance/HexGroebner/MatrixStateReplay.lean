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
public import HexGroebner.MatrixStateFuel

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


/-- The universal advance invariant replays through arbitrary bounded schedules,
including suspended and terminal calls, for this concrete prime-field input. -/
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

/-- Kernel replay covers every quantum and either scheduler after an arbitrary
bounded prefix, including zero-step prefixes and already completed prefixes. -/
theorem completion_example (steps quantum : Nat) (native : Bool) :
    let field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
    let row : SparseRow := ⟨⟨#[0,0,0,0,2,0,0,0]⟩,⟨#[2,1]⟩⟩
    let state := advance (start field {} 3 #[] #[row] #[2] false) steps
    let out := finishState quantum state native
    out.phase = .done ∧ out.result.isSome = true := by
  exact ⟨finishState_done _ quantum native (advance_geometry _ steps (start_geometry ..)),
    finishState_result _ quantum native (advance_geometry _ steps (start_geometry ..))
      (advance_closed _ steps (start_closed ..))⟩

/-- info: 'Hex.Groebner.MatrixStateReplay.completion_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms completion_example
/-- info: 'Hex.Groebner.MatrixState.finishState_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.finishState_done
/-- info: 'Hex.Groebner.MatrixState.finishState_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MatrixState.finishState_result

end Hex.Groebner.MatrixStateReplay
