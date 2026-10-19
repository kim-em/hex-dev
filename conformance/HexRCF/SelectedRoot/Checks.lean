/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.Refusals
import HexRealClosure.SignEvidence

open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests.Data Hex.RCF.SelectedRootTests.Upper Hex.RCF.SelectedRootTests.Controls
namespace Hex.RCF.SelectedRootTests.Checks
open Hex.RCF.SelectedRootTests

private def replace (j : Codec.Json) (index : Nat) (value : Codec.Json) :=
  Codec.Json.arr ((j.getArr?.toOption.getD #[]).set! index value)

private def crossedPacket : Codec.Json :=
  let fields := Literals.rowPacket.getArr?.toOption.getD #[]
  let binding := fields[1]?.getD (Codec.Json.arr #[])
  replace Literals.rowPacket 1
    (replace binding 0 (Tower.Signature.codec.encode base.signature))

def crossedContext : Bool :=
  !((Algebraic.SignEvidence.codec (Algebraic.Element.signCodec base.codec facts)
    Tower.Signature.codec raw).decode crossedPacket).isOk

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem context_checked : crossedContext = true := by decide +kernel

theorem negative_real : original.value negative = -Real.sqrt 2 := by
  unfold negative
  erw [Algebraic.Element.cachedNeg_eq]
  exact (original.neg alpha).trans (congrArg Neg.neg alpha_value)

theorem zero_real : original.value zeroGuard = Real.sqrt 2 - Real.sqrt 2 := by
  unfold zeroGuard
  erw [Algebraic.Element.cachedSub_eq]
  exact (original.sub alpha alpha).trans (congrArg₂ Sub.sub alpha_value alpha_value)

theorem falseAccepted : Row.evaluate facts values [] falseSchema packet = .ok false := by
  have accepted := Refusals.falseChecked
  change Decidable.decide (Row.evaluate facts values [] falseSchema packet = .ok false) = true at accepted
  exact of_decide_eq_true accepted

theorem counterexample : ∃ x : ℝ, ¬ falseSchema.toProp (Samples.valuation original values x) := by
  have accepted := falseAccepted
  erw [Row.evaluate_eq] at accepted
  exact SelectedFormula.row_false original values [] falseSchema context packet accepted

/-- info: 'Hex.RCF.SelectedRootTests.Checks.context_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms context_checked
/-- info: 'Hex.RCF.SelectedRootTests.Checks.negative_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negative_real
/-- info: 'Hex.RCF.SelectedRootTests.Checks.zero_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_real
/-- info: 'Hex.RCF.SelectedRootTests.Checks.falseAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms falseAccepted
/-- info: 'Hex.RCF.SelectedRootTests.Checks.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counterexample
end Hex.RCF.SelectedRootTests.Checks
