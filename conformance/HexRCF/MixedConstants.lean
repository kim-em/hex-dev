/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.NamedConstants
public meta import HexRCF.NamedConstants
public meta import HexRCF.RealCoefficients
public meta import HexRCF.ProofEvidence

public section

namespace Hex.RCF.MixedConstants

open Hex RealCoefficients
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

theorem pi_radical : ∀ x : ℝ, x ^ 2 + Real.pi - Real.sqrt 2 > 0 := by rcf

theorem pi_other_radical : ∀ x : ℝ, x ^ 2 + Real.pi - Real.sqrt 3 > 0 := by rcf

theorem exp_radical : ∀ x : ℝ,
    x ^ 2 + Real.exp 1 - (2 : ℝ) ^ (1 / 3 : ℝ) > 0 := by rcf

theorem exp_selected : ∀ x : ℝ,
    x ^ 2 + Real.exp 1 - CubeTwo.realAlgebraic.toReal > 0 := by rcf

theorem pi_positive_divisor : ∀ x : ℝ,
    x ^ 2 + 1 / (Real.pi - Real.sqrt 2) > 0 := by rcf

theorem pi_negative_divisor : ∀ x : ℝ,
    x ^ 2 - 1 / (Real.sqrt 2 - Real.pi) > 0 := by rcf

theorem pi_cancelled : ∀ x : ℝ,
    x ^ 2 + Real.pi + 0 / (Real.pi - Real.sqrt 2) > 0 := by rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + Real.pi + 0 / (Real.sqrt 2 - Real.sqrt 2) > 0 := by rcf

/-- error: rcf: original closed divisor remains unresolved in supplied bounds -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + Real.pi + 0 / (NamedConstants.unknown - Real.sqrt 2) > 0 := by rcf

example : True := by
  fail_if_success
    have : ∀ x : ℝ, x ^ 2 + Real.sqrt 2 - Real.pi > 0 := by rcf
  trivial

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x ∈ Set.Ioc (1 : ℝ) 0,
    x ^ 2 + Real.pi + 0 / (Real.sqrt 2 - Real.sqrt 2) > 0 := by rcf

end Hex.RCF.MixedConstants

run_meta do
  for name in [`Hex.RCF.MixedConstants.pi_radical, `Hex.RCF.MixedConstants.pi_other_radical,
      `Hex.RCF.MixedConstants.exp_radical,
      `Hex.RCF.MixedConstants.exp_selected, `Hex.RCF.MixedConstants.pi_positive_divisor,
      `Hex.RCF.MixedConstants.pi_negative_divisor, `Hex.RCF.MixedConstants.pi_cancelled] do
    unless ← Hex.RCF.ProofEvidence.contains name
        (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound ||
          e.isConstOf ``Hex.RCF.RealCoefficients.Replay.check_sound) do
      throwError "mixed constant proof did not use algebraic literal replay"
    for forbidden in [``Hex.RCF.RealCoefficients.rootInterval,
        ``Hex.RealAlgebraicNumber.approxBall, ``Hex.RCF.RealCoefficients.Replay.build,
        ``Hex.RCF.RealCoefficients.FieldBuild.produceWithin] do
      if ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf forbidden) then
        throwError "mixed constant proof embedded algebraic production"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.MixedConstants.pi_other_radical
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.Replay.check_sound) do
    throwError "mixed sqrt3 proof did not use prepared finite replay"

/-- info: 'Hex.RCF.MixedConstants.pi_radical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.pi_radical
/-- info: 'Hex.RCF.MixedConstants.pi_other_radical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.pi_other_radical
/-- info: 'Hex.RCF.MixedConstants.exp_radical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.exp_radical
/-- info: 'Hex.RCF.MixedConstants.exp_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.exp_selected
/-- info: 'Hex.RCF.MixedConstants.pi_positive_divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.pi_positive_divisor
/-- info: 'Hex.RCF.MixedConstants.pi_negative_divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.pi_negative_divisor
/-- info: 'Hex.RCF.MixedConstants.pi_cancelled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.pi_cancelled
