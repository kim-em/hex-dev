/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Quote
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open RootReplayConformance Hex.RCF.RealCoefficients.CellReplayTests.Schema
open Lean Meta Elab Command Term
namespace Hex.RCF.RealCoefficients.CellReplayTests.Valuation
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

def coordinates : Fin 1 → Data.base.Value := fun _ => 2
def leaf : RealFormula.Poly 2 := MvPoly.X 1 ^ 2 - MvPoly.X 0
def matrix : RealFormula.QF 2 := .and (.atom ⟨leaf, .ge⟩)
  (.and (.atom ⟨leaf, .le⟩) (.atom ⟨0, .eq⟩))
theorem queries : RepresentationSpecialize.prepare coordinates matrix =
    RepresentationSpecialize.prepare values formula := by decide +kernel

def rows : CellReplay.Evidence wholeResult coordinates matrix :=
  ⟨fun i => queries.symm ▸ Check.evidence.sections i, Check.evidence.sectors,
    fun cut => ⟨(Check.evidence.sectorRows cut).root,
      (Check.evidence.sectorRows cut).bound,
      queries.symm ▸ (Check.evidence.sectorRows cut).signs⟩⟩
#root_check CellReplay.check coordinates matrix [-1, 2] cert wholeResult rows .existsReal = .ok true => checked

theorem coefficient : Data.rational.value (coordinates 0) = Real.sqrt 4 := by
  change Data.rational.value (2 : Data.base.Value) = Real.sqrt 4
  calc
    Data.rational.value (2 : Data.base.Value) = (2 : ℝ) := Data.rational.nat 2
    _ = Real.sqrt 4 := by norm_num
theorem positive_guard : Data.rational.value (2 : Data.base.Value) = (2 : ℝ) :=
  Data.rational.nat 2

meta def prove (target : Expr) (guards : Array Expr) (identityOverride : Option Expr := none) : TermElabM Expr := do
  let source ← match ← Reify.prepare target with
    | .error error => throwError "{Hex.RealFormula.Reify.Error.toMessageData error}"
    | .ok source => pure source
  let valuation ← elabTerm (← `(fun i : Fin 1 => Data.rational.value (coordinates i))) none
  synthesizeSyntheticMVarsNoPostponing
  let expected ← mkEq (← instantiateMVars valuation) source.valuation
  let identity ← match identityOverride with
    | some identity => pure identity
    | none => elabTermEnsuringType (← `(by funext i; have h := Fin.eq_zero i; subst i; exact coefficient)) expected
  let checker ← elabTerm (← `(CellReplay.check coordinates matrix [-1, 2] cert wholeResult rows .existsReal)) none
  synthesizeSyntheticMVarsNoPostponing
  CellQuote.finish target (← instantiateMVars checker) (Lean.mkConst ``checked)
    (Lean.mkConst ``Data.rational) (← instantiateMVars identity) guards

elab "#cell_valuation_quote" : command => liftTermElabM do
  let target ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 4 ≥ 0 ∧ x ^ 2 - Real.sqrt 4 ≤ 0 ∧
    0 / (-1 : ℝ) + 0 / (2 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let guards := #[Lean.mkConst ``Check.negative_guard, Lean.mkConst ``positive_guard]
  let proof ← prove target guards
  let proof ← Hex.RCF.checkProof `Hex.RCF.RealCoefficients.CellReplayTests.Valuation.source target proof
  addDecl (.thmDecl {
    name := `Hex.RCF.RealCoefficients.CellReplayTests.Valuation.source
    levelParams := []
    type := target
    value := proof })
#cell_valuation_quote
#print axioms source

private meta def refuse (label : String) (target checker identity : Expr)
    (guards : Array Expr) (expected : String) : TermElabM Unit := do
  let before ← getMCtx
  let constants := (← getEnv).constants.map₂.toList.length
  let failed ← try
    let _ ← CellQuote.finish target checker (Lean.mkConst ``checked) (Lean.mkConst ``Data.rational) identity guards
    pure false
  catch error =>
    match error with
    | .error _ message =>
      unless (← message.toString) == expected do throw error
      logInfo m!"{label}: {message}"
      pure true
    | _ => throw error
  unless failed do throwError "invalid coefficient quotation accepted: {label}"
  let after ← getMCtx
  unless constants == (← getEnv).constants.map₂.toList.length &&
      before.mvarCounter == after.mvarCounter && before.lmvarCounter == after.lmvarCounter &&
      before.depth == after.depth && before.eAssignment.toList == after.eAssignment.toList &&
      before.lAssignment.toList == after.lAssignment.toList do
    throwError "failed coefficient quotation changed caller state"

elab "#cell_valuation_refusals" : command => liftTermElabM do
  let target ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 4 ≥ 0 ∧ x ^ 2 - Real.sqrt 4 ≤ 0 ∧
    0 / (-1 : ℝ) + 0 / (2 : ℝ) = 0))
  let wrong ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 9 ≥ 0 ∧ x ^ 2 - Real.sqrt 9 ≤ 0 ∧
    0 / (-1 : ℝ) + 0 / (2 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let wrong ← instantiateMVars wrong
  let .ok prepared ← Reify.prepare target | throwError "expected source recognition"
  let valuation ← elabTerm (← `(fun i : Fin 1 => Data.rational.value (coordinates i))) none
  synthesizeSyntheticMVarsNoPostponing
  let expected ← mkEq (← instantiateMVars valuation) prepared.valuation
  let identity ← elabTermEnsuringType (← `(by funext i; have h := Fin.eq_zero i; subst i; exact coefficient)) expected
  let checker ← elabTerm (← `(CellReplay.check coordinates matrix [-1, 2] cert wholeResult rows .existsReal)) none
  synthesizeSyntheticMVarsNoPostponing
  let identity ← instantiateMVars identity
  let checker ← instantiateMVars checker
  let negative := Lean.mkConst ``Check.negative_guard
  let positive := Lean.mkConst ``positive_guard
  refuse "reversed original divisors" (← instantiateMVars target) checker identity #[positive, negative]
    "rcf: handler CellQuote.guardIdentity proposed a proof of a different goal"
  refuse "wrong coefficient valuation" (← instantiateMVars wrong) checker identity #[negative, positive]
    "rcf: handler CellQuote.valuationIdentity proposed a proof of a different goal"
#cell_valuation_refusals
end Hex.RCF.RealCoefficients.CellReplayTests.Valuation
