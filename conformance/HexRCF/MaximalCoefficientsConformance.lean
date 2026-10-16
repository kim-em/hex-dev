/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.MaximalCoefficients
import HexRCF.RealCoefficients
import HexRCF.ProofEvidence

set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

/-- Require completion of every source inventory and kernel-equivalence check
in a fresh ordinary module, including after an interrupted producer module. -/
example : True := Hex.RCF.RealCoefficients.MaximalCoefficientsTests.complete

namespace Hex.RCF.MaximalCoefficientsConformance

theorem sum_positive : ∀ x : ℝ, x^2 + (Real.sqrt 2 + Real.sqrt 3) > 0 := by rcf

theorem square_positive : ∀ x : ℝ, x^2 + (Real.sqrt 2 + Real.sqrt 3)^2 > 0 := by rcf

theorem negative_witness : ∃ x : ℝ, x = -(Real.sqrt 2 + Real.sqrt 3) ∧ x < -3 := by rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ,
    x^2 + 0 * (1 / (Real.sqrt 2 - Real.sqrt 2)) = x^2 := by rcf

open Lean Meta Qq in
run_meta do
  for (name,soundness,coefficient) in #[
      (``sum_positive, ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound,
        q(Real.sqrt 2 + Real.sqrt 3)),
      (``square_positive, ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound,
        q((Real.sqrt 2 + Real.sqrt 3)^2)),
      (``negative_witness, ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound,
        q(-(Real.sqrt 2 + Real.sqrt 3)))] do
    let .thmInfo declaration ← getConstInfo name | throwError "missing maximal coefficient proof"
    let .ok source ← Hex.RCF.RealCoefficients.Reify.prepare declaration.type
      | throwError "actual maximal proof source was not recognized"
    unless source.coefficients.size == 1 && (← isDefEq source.coefficients[0]! coefficient) do
      throwError "actual tactic proof did not retain its maximal coefficient"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
    let seen ← Hex.RCF.ProofEvidence.projectDependencies #[name]
    unless seen.contains soundness do
      throwError "maximal coefficient goal omitted the actual real-coefficient checker"
  logInfo "closed sum, square and negative witness proofs use the real-coefficient checker"
  addDecl (.thmDecl {
    name := `Hex.RCF.MaximalCoefficientsConformance.proofsComplete
    levelParams := [], type := mkConst ``True, value := mkConst ``True.intro })

end Hex.RCF.MaximalCoefficientsConformance
