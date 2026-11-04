/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients
public import HexRCF.CertificationInputs
public meta import HexRCF.CertificationInputs
public meta import HexRCF.RealCoefficients
public meta import Lean.Elab.Tactic
public meta import Qq
public section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
open Hex Lean Meta Elab Qq
run_meta do
  let goals : Array (String × Expr × Bool × String) := #[
    ("rational", q(∀ x : ℝ, x^2 ≥ 0), true, ""),
    ("fourth-root", q(∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2), true, ""),
    ("mixed-quartic", q(∀ x : ℝ, x^2 + Hex.RCF.CertificationInputs.realAlgebraic.toReal + Real.sqrt 2 > 0), true, ""),
    ("mixed-false", q(∀ x : ℝ, x^2 < Hex.RCF.CertificationInputs.realAlgebraic.toReal + Real.sqrt 2), false, "universal sentence is false"),
    ("mixed-exhausted", q(∀ x : ℝ, x^2 + Hex.RCF.CertificationInputs.realAlgebraic.toReal + Real.sqrt 2 > 0), false, "common-field degree"),
    ("mixed-production-exhausted", q(∀ x : ℝ,
      x^2-(Hex.RCF.CertificationInputs.realAlgebraic.toReal+Real.sqrt 2)*x+
        Hex.RCF.CertificationInputs.realAlgebraic.toReal*Real.sqrt 2<0 → 1<x ∧ x<2),
      false, "algebraic interval refinement budget exhausted"),
    ("mixed-zero-divisor", q(∀ x : ℝ, x^2 + Hex.RCF.CertificationInputs.realAlgebraic.toReal + 0 / (Real.sqrt 2 - Real.sqrt 2) > 0), false, "original closed divisor is zero"),
    ("false", q(∀ x : ℝ, x^2 < Real.sqrt 2), false, "universal sentence is false"),
    ("zero-divisor", q(∀ x : ℝ, x^2 + 0 / (Real.sqrt 2 - Real.sqrt 2) ≥ 0), false, "original closed divisor is zero")]
  for (label, target, expected, diagnostic) in goals do
    let saved ← saveState
    let candidate ← mkFreshExprMVar target
    let declarations := (← getEnv).constants.map₂.toList.length
    let outcome ← try
      let remaining ← withOptions (fun options => if label == "mixed-exhausted" then
          options.set `rcf.algebraic.commonDegree (7 : Nat)
        else if label == "mixed-production-exhausted" then
          (options.set `rcf.algebraic.directDepth (0 : Nat)).set
            `rcf.algebraic.maxDoublings (0 : Nat)
        else options) do
        Elab.runTactic' candidate.mvarId! (← `(tactic| rcf))
      unless remaining.isEmpty do throwError "unsolved goals"
      let proof ← instantiateMVars candidate
      let _ ← Hex.RCF.checkProof `Compatibility target proof
      pure (true, "proved")
    catch e => pure (false, ← e.toMessageData.toString)
    unless outcome.1 do
      if ← candidate.mvarId!.isAssigned then
        throwError "failed tactic assigned its original goal: {label}"
      unless (← getEnv).constants.map₂.toList.length == declarations do
        throwError "failed tactic retained temporary declarations: {label}"
    saved.restore
    unless outcome.1 == expected do throwError "unexpected compatibility result {label}: {outcome.2}"
    unless expected || (outcome.2.splitOn diagnostic).length > 1 do
      throwError "unexpected diagnostic {label}: {outcome.2}"
    logInfo m!"CAS_COMPATIBILITY {label}: PASS"
