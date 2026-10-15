/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.AlgebraicPreparation
import HexRCF.ProofEvidence
open Hex Lean Meta Qq Hex.RCF.RealCoefficients
namespace Hex.RCF.AlgebraicPreparationConformance
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

private meta def nonnegative (source : Expr) : MetaM (Option Expr) := do
  let source : Q(ℝ) := source
  let goal ← mkFreshExprMVar q(0 ≤ $source)
  let remaining ← Elab.runTactic' goal.mvarId! (← `(tactic| norm_num))
  unless remaining.isEmpty do return none
  return some (← instantiateMVars goal)

private meta def checked (target : Expr) : MetaM AlgebraicPreparation.Environment := do
  let .ok prepared ← AlgebraicPreparation.prepare target nonnegative
    | throwError "native source preparation declined"
  for i in List.finRange prepared.source.coefficients.size do
    let item := prepared.coefficients[i]
    unless isPrivateName item.identity.getAppFn.constName! do
      throwError "native source preparation exported an unscoped auxiliary theorem"
    let _ ← withoutModifyingEnv <| Hex.RCF.checkProof `nativeCoefficient
      (← mkEq (← mkAppM ``RealAlgebraicNumber.toReal #[item.expression]) prepared.source.coefficients[i]) item.identity
  for i in List.finRange prepared.source.divisors.size do
    let item := prepared.divisors[i]
    unless isPrivateName item.identity.getAppFn.constName! do
      throwError "native divisor preparation exported an unscoped auxiliary theorem"
    let _ ← withoutModifyingEnv <| Hex.RCF.checkProof `nativeDivisor
      (← mkEq (← mkAppM ``RealAlgebraicNumber.toReal #[item.expression]) prepared.source.divisors[i]) item.identity
  return prepared

private meta def unchanged (action : MetaM Unit) : MetaM Unit := do
  let marker ← mkFreshExprMVar (mkConst ``Nat)
  let before := (← getMCtx).decls.toList.length
  action
  unless (← getMCtx).decls.toList.length == before && !(← marker.mvarId!.isAssigned) do
    throwError "failed native source preparation changed metavariable state"

run_meta do
  let target : Q(Prop) := q(∀ x : ℝ, x^2 + Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 > 0)
  let prepared ← checked target
  unless prepared.source.coefficients.size > 0 do throwError "independent algebraic source lost its coefficients"
  unless prepared.source.divisors.isEmpty do throwError "independent algebraic source acquired a divisor"
  for i in List.finRange prepared.source.coefficients.size do
    let item := prepared.coefficients[i]
    let type ← inferType item.identity
    let name := `Hex.RCF.AlgebraicPreparationConformance.identity ++ Name.num .anonymous i.val
    addDecl (.thmDecl {name,levelParams := [],type,value := item.identity})
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "native source identity has a forbidden axiom"
  -- The reifier's own source accounting fits exactly; the additional
  -- coefficient interpretation must consume the same aggregate budget.
  let config : Hex.RealFormula.Reify.Config := {}
  let config := {config with ring := {config.ring with budget :=
    {config.ring.budget with sourceNodes := prepared.source.usage.sourceNodes}}}
  unchanged do
    let .error (.budget exhausted) ← AlgebraicPreparation.prepare target nonnegative config
      | throwError "native preparation reset the aggregate source budget"
    unless exhausted.dimension == .sourceNodes do throwError "wrong native preparation exhaustion"
  -- A lying callback is checked as a proposition and cannot become evidence.
  unchanged do
    let name := `Hex.RCF.AlgebraicPreparationConformance.rollbackMarker
    unless !(← getEnv).contains name do throwError "rollback marker already exists"
    let .error (.internal _) ← AlgebraicPreparation.prepare target (fun _ => do
      unless (← getEnv).contains name do
        let type ← mkEq (mkNatLit 0) (mkNatLit 0)
        addDecl (.thmDecl {name,levelParams := [],type,value := ← mkEqRefl (mkNatLit 0)})
      return some (← mkEqRefl (mkNatLit 0)))
      | throwError "native preparation accepted a wrong nonnegativity proof"
    unless !(← getEnv).contains name do throwError "failed native source preparation leaked a declaration"
  unchanged do
    let .error (.unsupported _ _) ← AlgebraicPreparation.prepare q(∀ x : ℝ, x^2 + Real.pi > 0) nonnegative
      | throwError "unregistered constant entered the exact algebraic producer"
  unchanged do
    let .error (.unsupported _ _) ← AlgebraicPreparation.prepare q(∀ x : ℝ, 1 / x = 0) nonnegative
      | throwError "variable denominator entered the exact algebraic producer"
  -- Observe exception rollback without allowing the test observer to restore
  -- state on behalf of the production API.
  unchanged do
    let result ← tryCatchRuntimeEx
      (some <$> AlgebraicPreparation.prepare q(∀ _ : ℝ, 0 / (Real.sqrt 2 - Real.sqrt 2) = 0) nonnegative)
      (fun _ => pure none)
    if let some (.ok prepared) := result then
      match prepared.build (fun _ => none) with
      | .error .divisor => pure ()
      | _ => throwError "cancelled original zero divisor entered native root production"
  let guarded ← checked q(∀ _ : ℝ, 0 / (Real.sqrt 2 + 1) = 0 ∧ 0 / (Real.sqrt 3 + 1) = 0)
  unless guarded.source.divisors.size == 2 do
    throwError "native preparation erased independent original divisors"
  unless guarded.guards.map Fin.val ==
      [guarded.source.coefficients.size,guarded.source.coefficients.size+1] do
    throwError "native preparation reordered original guards"
  for i in List.finRange guarded.source.divisors.size do
    unless guarded.inputs (Fin.natAdd guarded.source.coefficients.size i) == guarded.divisors[i].proposal do
      throwError "native preparation changed original guard coordinates"
  let interval ← checked q(∃ x ∈ Set.Ioc (1 : ℝ) 2, x^2 = Real.sqrt 2)
  unless interval.quantifier == .existsReal && interval.formula.polys.length >= 3 do
    throwError "native preparation lost the shared half-open domain atoms"
  for (target,expected) in [
      (q(∀ _ : ℝ, 0 / (-1 : ℝ) = 0),true),
      (q(∀ _ : ℝ, 0 / (-1 : ℝ) = 1),false)] do
    let constantInput ← checked target
    unless constantInput.source.coefficients.isEmpty && constantInput.source.divisors.size == 1 do
      throwError "native preparation erased a rational guard-only input"
    let registry : RealClosure.BaseContext.Registry := fun _ => none
    let .ok ⟨sources,shared,packet⟩ := constantInput.build registry
      | throwError "guard-only prepared source did not produce a native packet"
    let input := packet.family.collection.input
    for quantifier in [RealFormula.Quantifier.existsReal,.forallReal] do
      unless (CompleteReplay.check input.context.codec
          (input.value ∘ GatherCells.values shared (AlgebraicCells.coefficients sources constantInput.indices))
          constantInput.formula ((GatherCells.guards shared (AlgebraicCells.guards sources constantInput.guards)).map input.value)
          packet.radical quantifier packet.rootGraph packet.cells).toOption == some expected do
        throwError "guard-only prepared source changed its checked constant verdict"
  logInfo "native source identities, ordered guard-only inputs, aggregate budget and transactional refusals checked"
end Hex.RCF.AlgebraicPreparationConformance
