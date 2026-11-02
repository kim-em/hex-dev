/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebnerStateNative
-- Inspect logical loop bodies only; states are created exclusively by start.
import all HexGroebner.MatrixState
import all Init.Data.Range.Basic

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

/-- Residual validation follows the same input indices as the continuation. -/
private noncomputable def validateFrom (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (cursor : Nat) : Matrix.Work Unit := do
  for i in [cursor:reducers.size+targets.size] do
    Matrix.validate field limits columns i
      (if i < reducers.size then reducers[i]! else targets[i-reducers.size]!)

private theorem validate_tail (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (cursor : Nat)
    (h : cursor < reducers.size+targets.size) :
    validateFrom field limits columns reducers targets cursor = (do
      Matrix.validate field limits columns cursor
        (if cursor < reducers.size then reducers[cursor]! else targets[cursor-reducers.size]!)
      validateFrom field limits columns reducers targets (cursor+1)) := by
  simp only [validateFrom, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  have length : reducers.size+targets.size-cursor =
      (reducers.size+targets.size-(cursor+1))+1 := by omega
  rw [length, List.range'_succ]
  simp

private theorem validate_done (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (cursor : Nat)
    (h : reducers.size+targets.size ≤ cursor) :
    validateFrom field limits columns reducers targets cursor = pure () := by
  simp [validateFrom, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_eq_zero_of_le h]

private theorem validate_error_run (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (cursor : Nat)
    (stats nextStats : MatrixStats) (error : MatrixError)
    (h : cursor < reducers.size+targets.size)
    (hrow : (Matrix.validate field limits columns cursor
      (if cursor < reducers.size then reducers[cursor]! else targets[cursor-reducers.size]!)).run
        stats = (.error error,nextStats)) :
    (validateFrom field limits columns reducers targets cursor).run stats =
      (.error error,nextStats) := by
  rw [validate_tail field limits columns reducers targets cursor h]
  dsimp [ExceptT.run, Bind.bind, ExceptT.bind, ExceptT.bindCont,
    ExceptT.mk, StateT.bind, Pure.pure, StateT.pure]
  simp only [ExceptT.run] at hrow
  rw [hrow] <;> rfl

private theorem validate_ok_run (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (cursor : Nat)
    (stats nextStats : MatrixStats)
    (h : cursor < reducers.size+targets.size)
    (hrow : (Matrix.validate field limits columns cursor
      (if cursor < reducers.size then reducers[cursor]! else targets[cursor-reducers.size]!)).run
        stats = (.ok (),nextStats)) :
    (validateFrom field limits columns reducers targets cursor).run stats =
      (validateFrom field limits columns reducers targets (cursor+1)).run nextStats := by
  rw [validate_tail field limits columns reducers targets cursor h]
  dsimp [ExceptT.run, Bind.bind, ExceptT.bind, ExceptT.bindCont,
    ExceptT.mk, StateT.bind, Pure.pure, StateT.pure]
  simp only [ExceptT.run] at hrow
  rw [hrow] <;> rfl

end Hex.Groebner.MatrixStateReplay
