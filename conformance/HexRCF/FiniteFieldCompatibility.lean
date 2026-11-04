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
    ("remaining-frontend-gap", q(∀ x : ℝ, x^2 + Hex.RCF.CertificationInputs.realAlgebraic.toReal + Real.sqrt 2 > 0), false, "no checked irreducibility witness"),
    ("false", q(∀ x : ℝ, x^2 < Real.sqrt 2), false, "universal sentence is false"),
    ("zero-divisor", q(∀ x : ℝ, x^2 + 0 / (Real.sqrt 2 - Real.sqrt 2) ≥ 0), false, "original closed divisor is zero")]
  for (label, target, expected, diagnostic) in goals do
    let saved ← saveState
    let outcome ← try
      let candidate ← mkFreshExprMVar target
      let remaining ← Elab.runTactic' candidate.mvarId! (← `(tactic| rcf))
      unless remaining.isEmpty do throwError "unsolved goals"
      let proof ← instantiateMVars candidate
      let _ ← Hex.RCF.checkProof `Compatibility target proof
      pure (true, "proved")
    catch e => pure (false, ← e.toMessageData.toString)
    saved.restore
    unless outcome.1 == expected do throwError "unexpected compatibility result {label}: {outcome.2}"
    unless expected || (outcome.2.splitOn diagnostic).length > 1 do
      throwError "unexpected diagnostic {label}: {outcome.2}"
    logInfo m!"CAS_COMPATIBILITY {label}: PASS"
