/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Quote
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open RootReplayConformance Hex.RCF.RealCoefficients.CellReplayTests.Schema Hex.RCF.RealCoefficients.CellReplayTests.Check
open Lean Meta Elab Command Term
namespace Hex.RCF.RealCoefficients.CellReplayTests.Controls
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
private def refuse (label : String) (target accepted : Expr) (expectedMessage : String) (checkerOverride : Option Expr := none)
    (guardIdentities : Array Expr := #[]) : TermElabM Unit := do
  let source ← match ← Reify.prepare target with
    | .error error => throwError "{Hex.RealFormula.Reify.Error.toMessageData error}"
    | .ok source => pure source
  let valuation ← elabTerm (← `(fun i : Fin 0 => Data.rational.value (values i))) none
  synthesizeSyntheticMVarsNoPostponing
  let valuation ← instantiateMVars valuation
  let type ← mkEq valuation source.valuation
  let identity ← elabTermEnsuringType (← `(by funext i; exact Fin.elim0 i)) type
  let checker ← match checkerOverride with
    | some checker => pure checker
    | none => elabTerm (← `(CellReplay.check values formula [] cert wholeResult evidence .existsReal)) none
  synthesizeSyntheticMVarsNoPostponing
  let checker ← instantiateMVars checker
  let identity ← instantiateMVars identity
  let before ← getMCtx
  let constants := (← getEnv).constants.map₂.toList.length
  let failed ← try
    let _ ← CellQuote.finish target checker accepted (mkConst ``Data.rational) identity guardIdentities
    pure false
  catch error =>
    match error with
    | .error _ message =>
      unless (← message.toString) == expectedMessage do throw error
      logInfo m!"{label}: {message}"
      pure true
    | _ => throw error
  unless failed do throwError "invalid cell quotation accepted: {label}"
  let after ← getMCtx
  unless constants == (← getEnv).constants.map₂.toList.length do throwError "failed cell quotation changed environment"
  unless before.mvarCounter == after.mvarCounter && before.lmvarCounter == after.lmvarCounter &&
      before.depth == after.depth && before.eAssignment.toList == after.eAssignment.toList &&
      before.lAssignment.toList == after.lAssignment.toList do
    throwError "failed cell quotation changed metavariable state"

elab "#cell_quote_refusals" : command => liftTermElabM do
  let original ← elabType (← `(∃ x : ℝ, x ^ 2 - 2 ≥ 0 ∧ x ^ 2 - 2 ≤ 0 ∧ (0 : ℝ) = 0))
  let wrong ← elabType (← `(∃ x : ℝ, x ^ 2 - 3 ≥ 0 ∧ x ^ 2 - 3 ≤ 0 ∧ (0 : ℝ) = 0))
  let universal ← elabType (← `(∀ x : ℝ, x ^ 2 - 2 ≥ 0 ∧ x ^ 2 - 2 ≤ 0 ∧ (0 : ℝ) = 0))
  let zero ← elabType (← `(∃ x : ℝ, x ^ 2 - 2 ≥ 0 ∧ x ^ 2 - 2 ≤ 0 ∧ 0 / (2 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let accepted : Expr := Lean.mkConst ``Hex.RCF.RealCoefficients.CellReplayTests.Check.exists_checked
  refuse "wrong polynomial source" (← instantiateMVars wrong) accepted
    "rcf: checked formula has a different polynomial leaf"
  refuse "wrong quantifier" (← instantiateMVars universal) accepted
    "rcf: checked formula has a different source syntax"
  refuse "diagnostic false" (← instantiateMVars original) (mkConst ``Hex.RCF.RealCoefficients.CellReplayTests.Check.exists_false)
    "rcf: handler CellQuote.accepted proposed a proof of a different goal"
  refuse "omitted original divisor" (← instantiateMVars zero) accepted
    "rcf: cell checker has a different original divisor identity count"
  let guarded ← elabType (← `(∃ x : ℝ, x ^ 2 - 2 ≥ 0 ∧ x ^ 2 - 2 ≤ 0 ∧ 0 / (-1 : ℝ) = 0))
  let program ← elabTerm (← `(CellReplay.check values formula [-1] cert wholeResult evidence .existsReal)) none
  synthesizeSyntheticMVarsNoPostponing
  let guarded ← instantiateMVars guarded
  let program ← instantiateMVars program
  let checked : Expr := Lean.mkConst ``Hex.RCF.RealCoefficients.CellReplayTests.Check.guarded_checked
  let identity : Expr := Lean.mkConst ``Hex.RCF.RealCoefficients.CellReplayTests.Check.negative_guard
  refuse "missing negative guard identity" guarded checked
    "rcf: cell checker has a different original divisor identity count" (some program)
  refuse "extra negative guard identity" guarded checked
    "rcf: cell checker has a different original divisor identity count" (some program) #[identity, identity]
  refuse "wrong negative guard identity" guarded checked
    "rcf: handler CellQuote.guardIdentity proposed a proof of a different goal" (some program)
    #[← mkEqRefl (mkNatLit 0)]

  refuse "omitted checker divisor" guarded (Lean.mkConst ``Hex.RCF.RealCoefficients.CellReplayTests.Check.exists_checked)
    "rcf: cell checker has a different original divisor count" none #[identity]
  let extra ← elabTerm (← `(CellReplay.check values formula [-1, 2] cert wholeResult evidence .existsReal)) none
  synthesizeSyntheticMVarsNoPostponing
  refuse "extra checker divisor" guarded (Lean.mkConst ``Hex.RCF.RealCoefficients.CellReplayTests.Check.extra_checked)
    "rcf: cell checker has a different original divisor count" (some (← instantiateMVars extra)) #[identity]

#cell_quote_refusals
end Hex.RCF.RealCoefficients.CellReplayTests.Controls
