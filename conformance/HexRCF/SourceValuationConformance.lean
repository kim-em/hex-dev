/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.CellQuote
import HexRCF.RealCoefficients.TowerCompile
import HexRCF.RealCoefficients.FieldLiteral
import HexRCF.SelectedRoot.Data

open Lean Meta Qq Hex Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private meta def leaf (source : Expr) : Hex.RealFormula.Reify.ReifyM (Option TowerCompile.Term) := do
  if source == q(Real.sqrt 2) then
    return some ⟨mkConst ``Data.alpha,mkConst ``Data.alpha_value⟩
  return none

run_meta do
  let targets : Array Expr := #[q(∀ x : ℝ, x^2 ≥ 0),
      q(∀ x : ℝ, x^2 + Real.sqrt 2 > 0),
      q(∀ x : ℝ, x^2 + x * (Real.sqrt 2 + 1) + (Real.sqrt 2 + 2) > 0)]
  for i in List.finRange targets.size do
    let target := targets[i]
    let .ok source ← Reify.prepare target | throwError "valuation source did not prepare"
    let .ok result ← RootQuote.runWith (do
        let (coefficients,_) ← TowerCompile.prepareWith source (mkConst ``Data.original) leaf
        let zero ← TowerCompile.compile (mkConst ``Data.original) leaf q((0 : ℝ))
        let values ← FieldLiteral.finiteExpr (← inferType zero.expression)
          (coefficients.map (·.expression)) zero.expression
        let proof ← CellQuote.valuationWith source (mkConst ``Data.original)
          values (coefficients.map (·.proof))
        pure ⟨values,proof,(← get).budget.consumed⟩) {} source.usage
      | throwError "ordered valuation proof was declined"
    let name := Name.num `Hex.RCF.SourceValuationConformance.quoted i.val
    addDecl (.thmDecl {name,levelParams := [],type := ← inferType result.proof,value := result.proof})
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "source valuation has a forbidden axiom"
    logInfo m!"source valuation coordinates={source.coefficients.size}; proofNodes={result.usage.proofNodes}"

run_meta do
  let .ok source ← Reify.prepare q(∀ x : ℝ,
      x^2 + x * (Real.sqrt 2 + 1) + (Real.sqrt 2 + 2) > 0)
    | throwError "permutation control did not prepare"
  for mode in [0,1,2,3] do
    let rejected ← try
      let _ ← RootQuote.runWith (do
        let (coefficients,_) ← TowerCompile.prepareWith source (mkConst ``Data.original) leaf
        let zero ← TowerCompile.compile (mkConst ``Data.original) leaf q((0 : ℝ))
        let entries := if mode == 0 then coefficients.reverse
          else if mode == 3 then coefficients.extract 0 1 else coefficients
        let proofs := if mode == 1 then (coefficients.map (·.proof)).reverse
          else if mode == 2 then (coefficients.map (·.proof)).extract 0 1
          else coefficients.map (·.proof)
        let values ← FieldLiteral.finiteExpr (← inferType zero.expression)
          (entries.map (·.expression)) zero.expression
        let proof ← CellQuote.valuationWith source (mkConst ``Data.original) values proofs
        pure ⟨values,proof,(← get).budget.consumed⟩) {} source.usage
      pure false
    catch _ => pure true
    unless rejected do throwError "valuation accepted a swapped coordinate/proof or missing entry"
  logInfo "swapped coordinates/proofs, missing entries and wrong coordinate counts rejected"

run_meta do
  let .ok source ← Reify.prepare q(∀ x : ℝ, x^2 + Real.sqrt 2 > 0)
    | throwError "unresolved-coordinate source failed to prepare"
  let domain ← mkAppM ``Fin #[mkNatLit source.coefficients.size]
  let carrier ← mkAppM ``RealClosure.Tower.Context.Value #[mkConst ``Data.parent]
  let values ← mkFreshExprMVar (← mkArrow domain carrier)
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let rejected ← try
    let _ ← RootQuote.runWith (do
      let (coefficients,_) ← TowerCompile.prepareWith source (mkConst ``Data.original) leaf
      let proof ← CellQuote.valuationWith source (mkConst ``Data.original) values
        (coefficients.map (·.proof))
      pure ⟨values,proof,(← get).budget.consumed⟩) {} source.usage
    pure false
  catch _ => pure true
  unless rejected do throwError "unresolved source coordinates were accepted"
  if ← values.mvarId!.isAssigned then throwError "valuation construction assigned caller coordinates"
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "failed valuation construction retained declarations"
  logInfo "unresolved coordinates rejected without metavariable or declaration changes"

namespace Hex.RCF.SourceValuationConformance
theorem runFinished : True := trivial
end Hex.RCF.SourceValuationConformance
