/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.TowerCompile
import HexRCF.SelectedRoot.Data

open Lean Meta Qq Hex Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private meta def leaf (source : Expr) : Hex.RealFormula.Reify.ReifyM (Option TowerCompile.Term) := do
  if source == q(Real.sqrt 2) then
    return some ⟨mkConst ``Data.alpha,mkConst ``Data.alpha_value⟩
  return none

private meta def action (source : Expr) : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
  let term ← TowerCompile.compile (mkConst ``Data.original) leaf source
  return ⟨term.expression,term.proof,(← get).budget.consumed⟩

run_meta do
  let sources : Array Expr := #[q((2 : ℝ)),q((-3 : ℝ)),q((1 / 7 : ℝ)),
    q(((3 / 2 : ℚ) : ℝ)),q(Real.sqrt 2 + 3),q(Real.sqrt 2 - 1),
    q((Real.sqrt 2 - 1)^3 / (Real.sqrt 2 + 1)),q((Real.sqrt 2)⁻¹),
    q((Real.sqrt 2)^0)]
  for i in List.finRange sources.size do
    let source := sources[i]
    let .ok result ← RootQuote.runWith (action source)
      | throwError "tower arithmetic quotation declined a supported source"
    let target ← mkEq (← mkAppM ``RealClosure.Tower.Model.value
      #[mkConst ``Data.original,result.value]) source
    unless ← isDefEq (← inferType result.proof) target do
      throwError "tower arithmetic quotation changed its source"
    let name := Name.num `Hex.RCF.TowerCompileConformance.quoted i.val
    addDecl (.thmDecl {name,levelParams := [],type := target,value := result.proof})
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "tower arithmetic quotation has a forbidden axiom"
    logInfo m!"tower source {source}: proofNodes={result.usage.proofNodes}"

run_meta do
  let .ok _ ← RootQuote.runWith (do
      let marker ← mkFreshExprMVar (mkConst ``Nat)
      let declaration ← mkFreshUserName `declinedLeaf
      let decline := fun (_ : Expr) => do
        marker.mvarId!.assign (mkNatLit 42)
        let _ ← mkAuxDefinition declaration (mkConst ``Nat) (mkNatLit 42) (compile := false)
        pure (none : Option TowerCompile.Term)
      let term ← TowerCompile.compile (mkConst ``Data.original) decline q((3 : ℝ))
      if ← marker.mvarId!.isAssigned then throwError "declined leaf assigned caller metavariable"
      if (← getEnv).contains declaration then throwError "declined leaf retained a declaration"
      pure ⟨term.expression,term.proof,(← get).budget.consumed⟩)
    | throwError "declining leaf unexpectedly rejected rational compilation"
  logInfo "declining leaf restored metavariables and declarations inside the request"

run_meta do
  let before ← saveState
  let rejected ← try
    let _ ← RootQuote.runWith (do
      let term ← TowerCompile.compile (mkConst ``Data.original)
        (fun _ => pure (some ⟨mkConst ``Data.alpha,mkConst ``Data.alpha_value⟩)) q((0 : ℝ))
      pure ⟨term.expression,term.proof,(← get).budget.consumed⟩)
    pure false
  catch _ => pure true
  unless rejected do throwError "wrong source identity was accepted"
  before.restore
  let config : Hex.RealFormula.Reify.Config := {}
  let config := {config with ring := {config.ring with budget :=
    {config.ring.budget with proofNodes := 1}}}
  let .error (.budget _) ← RootQuote.runWith (action q(Real.sqrt 2 + 1)) config
    | throwError "tower source quotation did not preserve budget refusal"
  logInfo "wrong source identity rejected and aggregate budget refusal retained"

run_meta do
  for original in #[q(∀ x : ℝ, x^2 + (Real.sqrt 2 + 1) / (Real.sqrt 2 - 1) > 0),
      q(∀ x : ℝ, x^2 + x * ((Real.sqrt 2 + 1) / (Real.sqrt 2 - 1)) +
        (Real.sqrt 2 + 2) / (Real.sqrt 2 + 3) > 0),
      q(∀ x : ℝ, x^2 + 0 * (1 / (Real.sqrt 2 - Real.sqrt 2)) ≥ 0)] do
    let .ok source ← Reify.prepare original
      | throwError "source preparation rejected the ordered-inventory control"
    unless source.divisors.size > 0 do throwError "source preparation lost the original guard"
    let .ok _ ← RootQuote.runWith (do
        let (coefficients,divisors) ← TowerCompile.prepareWith source (mkConst ``Data.original) leaf
        unless coefficients.size == source.coefficients.size && divisors.size == source.divisors.size do
          throwError "tower preparation changed an original inventory"
        for i in List.finRange source.coefficients.size do
          let some coefficient := coefficients[i.val]? | throwError "missing compiled coefficient"
          let target ← mkEq (← mkAppM ``RealClosure.Tower.Model.value
            #[mkConst ``Data.original,coefficient.expression]) source.coefficients[i]
          unless ← isDefEq (← inferType coefficient.proof) target do
            throwError "tower preparation changed original coefficient order"
        for i in List.finRange source.divisors.size do
          let some divisor := divisors[i.val]? | throwError "missing compiled divisor"
          let target ← mkEq (← mkAppM ``RealClosure.Tower.Model.value
            #[mkConst ``Data.original,divisor.expression]) source.divisors[i]
          unless ← isDefEq (← inferType divisor.proof) target do
            throwError "tower preparation changed original divisor order"
        logInfo m!"ordered tower inventory: {coefficients.size} coefficients, {divisors.size} original guards"
        let some divisor := divisors[0]? | throwError "missing original divisor"
        pure ⟨divisor.expression,divisor.proof,(← get).budget.consumed⟩) {} source.usage
      | throwError "tower preparation declined an authenticated source inventory"
    let .error (.internal _) ← RootQuote.runWith (do
        let _ ← TowerCompile.prepareWith source (mkConst ``Data.original) leaf
        throwError "unexpectedly reset source accounting")
      | throwError "tower preparation accepted a reset source budget"
  logInfo "original guard inventories survive zero multiplication; reset source budgets rejected"

run_meta do
  let marker ← mkFreshExprMVar (mkConst ``Nat)
  let declaration ← mkFreshUserName `failedTowerLeaf
  let failed ← try
    let _ ← RootQuote.runWith (do
      let term ← TowerCompile.compile (mkConst ``Data.original) (fun _ => do
        marker.mvarId!.assign (mkNatLit 42)
        let _ ← mkAuxDefinition declaration (mkConst ``Nat) (mkNatLit 42) (compile := false)
        throwError "deliberate leaf failure") q(Real.sqrt 2)
      pure ⟨term.expression,term.proof,(← get).budget.consumed⟩)
    pure false
  catch _ => pure true
  unless failed do throwError "leaf failure was swallowed"
  if ← marker.mvarId!.isAssigned then throwError "failed leaf retained a metavariable assignment"
  if (← getEnv).contains declaration then throwError "failed leaf retained a declaration"
  let swapped ← try
    let _ ← RootQuote.runWith (do
      let term ← TowerCompile.compile (mkConst ``Data.rational) leaf q(Real.sqrt 2)
      pure ⟨term.expression,term.proof,(← get).budget.consumed⟩)
    pure false
  catch _ => pure true
  unless swapped do throwError "coefficient proof accepted a different context model"
  let .error (.unsupported _ _) ← RootQuote.runWith (action q(Real.sin (0 : ℝ)))
    | throwError "arbitrary closed function entered coefficient arithmetic"
  logInfo "terminal leaf failure restored state; swapped model and unsupported function rejected"

run_meta do
  let .ok source ← Reify.prepare q(∀ x : ℝ, x^2 ≥ 0)
    | throwError "empty-inventory source preparation failed"
  unless source.coefficients.isEmpty && source.divisors.isEmpty do
    throwError "rational empty-inventory control acquired a coefficient"
  let rejected ← try
    let _ ← RootQuote.runWith (do
      let _ ← TowerCompile.prepareWith source (mkNatLit 0) leaf
      let zero := mkNatLit 0
      pure ⟨zero,← mkEqRefl zero,(← get).budget.consumed⟩) {} source.usage
    pure false
  catch _ => pure true
  unless rejected do throwError "empty inventories bypassed model validation"
  logInfo "empty coefficient/divisor inventories still validate the retained real model"

run_meta do
  let .ok source ← Reify.prepare q(∀ x : ℝ, x^2 + Real.sqrt 2 > 0)
    | throwError "transferred source-budget control failed to prepare"
  unless source.usage.sourceNodes > 0 do throwError "source-budget control recorded no work"
  let config : Hex.RealFormula.Reify.Config := {}
  let config := {config with ring := {config.ring with budget :=
    {config.ring.budget with sourceNodes := source.usage.sourceNodes - 1}}}
  let .error (.budget exhausted) ← RootQuote.runWith (do
      let (coefficients,_) ← TowerCompile.prepareWith source (mkConst ``Data.original) leaf
      let some term := coefficients[0]? | throwError "source-budget control lost its coefficient"
      pure ⟨term.expression,term.proof,(← get).budget.consumed⟩) config source.usage
    | throwError "transferred source usage exceeded its new request's limit"
  unless exhausted.dimension == .sourceNodes do throwError "wrong transferred-budget refusal"
  logInfo "transferred source usage is checked against every enclosing limit"

namespace Hex.RCF.TowerCompileConformance
theorem runFinished : True := trivial
end Hex.RCF.TowerCompileConformance
