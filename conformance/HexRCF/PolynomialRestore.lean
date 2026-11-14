/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.PolynomialTactic
public meta import HexRCF.PolynomialTactic
public meta import HexRCF.RealCoefficients
public meta import Lean.Elab.Tactic
public meta import Qq
public section

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Lean Meta Elab Qq Hex Hex.RCF.RealCoefficients

run_meta withoutExporting do
  let tests : Array (String × Expr × Bool) := #[
    ("false", q(∀ x : ℝ, (x^2 - Real.pi)^2 < 0), false),
    ("exhausted", q(∃ x : ℝ, x^2 = Real.pi ∧ 1 < x ∧ x < 2), true),
    ("zero-divisor", q(∃ x : ℝ, x^2 = Real.pi ∧ 0/(Real.pi-Real.pi)=0), false)]
  for (label, target, exhaust) in tests do
    let saved ← saveState
    let candidate ← mkFreshExprMVar target
    let declarations := (← getEnv).constants.map₂.toList.length
    let failed ← try
      let _ ← withOptions (fun options => if exhaust then
          options.set `rcf.algebraic.directDepth (0 : Nat) else options) do
        Elab.runTactic' candidate.mvarId! (← `(tactic| rcf))
      pure false
    catch _ => pure true
    unless failed do throwError "polynomial refusal unexpectedly succeeded: {label}"
    if ← candidate.mvarId!.isAssigned then
      throwError "polynomial refusal assigned the original goal: {label}"
    unless (← getEnv).constants.map₂.toList.length == declarations do
      throwError "polynomial refusal retained temporary declarations: {label}"
    saved.restore
    logInfo m!"POLYNOMIAL_RESTORE {label}: original goal and environment retained"
  let target : Q(Prop) := q(∃ x : ℝ, x^2=Real.pi ∧ 1<x ∧ x<2)
  let prepared ← Finite.prepare target
  let native ← FieldRuntime.evalFormula prepared.source.coefficients.size prepared.source.formula
  let .quant quantifier (.matrix formula) := native | throwError "expected one-quantifier source"
  if size : prepared.coefficients.size = prepared.source.coefficients.size then
    let bounds : Fin prepared.source.coefficients.size → Hex.OrderedFn.Oracle.Bounds :=
      fun i => prepared.coefficients[i.val]'(by omega) |>.bounds
    let some certificate := PolynomialBuild.build bounds formula 64 |
      throwError "replay restoration setup failed"
    let saved ← saveState
    let declarations := (← getEnv).constants.map₂.toList.length
    -- A corrupt lookup must fail preflight before any proposed source proof.
    let failed ← try
      let _ ← PolynomialLiteral.check bounds formula quantifier
        {certificate with index := .empty} (mkConst ``True) (mkConst ``True)
        (mkConst ``True) (mkConst ``True)
      pure false
    catch _ => pure true
    unless failed && (← getEnv).constants.map₂.toList.length == declarations do
      throwError "polynomial replay failure retained temporary declarations"
    saved.restore
    logInfo "POLYNOMIAL_RESTORE corrupt replay: complete state retained"
    let some first := prepared.coefficients[0]? | throwError "expected a pi coefficient"
    let boundsExpr ← FieldLiteral.finiteExpr (mkConst ``Hex.OrderedFn.Oracle.Bounds)
      (prepared.coefficients.map (·.literal)) first.literal
    let matrix ← whnf (← whnf prepared.source.formula).getAppArgs.back!
    let formulaExpr := matrix.getAppArgs.back!
    let saved ← saveState
    let declarations := (← getEnv).constants.map₂.toList.length
    -- This reaches quotation and kernel checks, then fails the final theorem
    -- application because the supplied containment proves a different goal.
    let failed ← try
      let _ ← PolynomialLiteral.check bounds formula quantifier certificate boundsExpr
        prepared.source.valuation (mkConst ``True.intro) formulaExpr
      pure false
    catch _ => pure true
    unless failed && (← getEnv).constants.map₂.toList.length == declarations do
      throwError "late polynomial replay failure retained temporary declarations"
    saved.restore
    logInfo "POLYNOMIAL_RESTORE wrong containment after quotation: complete state retained"
  else throwError "source coefficient count changed"
