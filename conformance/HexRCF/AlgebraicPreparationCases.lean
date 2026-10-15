/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.AlgebraicPreparation
open Hex Lean Meta Qq Hex.RCF.RealCoefficients
namespace Hex.RCF.AlgebraicPreparationConformance
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

private meta def checked (target : Expr) : MetaM AlgebraicPreparation.Inputs := do
  let .ok prepared ← AlgebraicPreparation.prepare target
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

-- Test-only observer at the underlying EIO layer: Core's ordinary handlers
-- intentionally rethrow interrupts. Shared state references are retained, so
-- this observer cannot perform rollback on behalf of the production API.
private meta def observeTerminal (action : MetaM α) (handler : Exception → MetaM α) : MetaM α :=
  fun metaContext metaState coreContext coreState => do
    try
      action metaContext metaState coreContext coreState
    catch error =>
      handler error metaContext metaState coreContext coreState

private meta def unchanged (action : MetaM Unit) : MetaM Unit := do
  let before := (← getMCtx).decls.toList.length
  action
  unless (← getMCtx).decls.toList.length == before do
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
  let .ok _ ← Reify.prepare target config
    | throwError "source-only reification no longer fits the aggregate budget control"
  unchanged do
    let .error (.budget exhausted) ← AlgebraicPreparation.prepare target (config := config)
      | throwError "native preparation reset the aggregate source budget"
    unless exhausted.dimension == .sourceNodes do throwError "wrong native preparation exhaustion"
  -- A lying callback is checked as a proposition and cannot become evidence.
  unchanged do
    let name := `Hex.RCF.AlgebraicPreparationConformance.rollbackMarker
    unless !(← getEnv).contains name do throwError "rollback marker already exists"
    let .error (.internal _) ← AlgebraicPreparation.prepare target (fun _ => do
      unless (← getEnv).contains name do
        let _ ← mkFreshExprMVar (mkConst ``Nat)
        let type ← mkEq (mkNatLit 0) (mkNatLit 0)
        addDecl (.thmDecl {name,levelParams := [],type,value := ← mkEqRefl (mkNatLit 0)})
      return some (← mkEqRefl (mkNatLit 0)))
      | throwError "native preparation accepted a wrong nonnegativity proof"
    unless !(← getEnv).contains name do throwError "failed native source preparation leaked a declaration"
  unchanged do
    let .error (.unsupported _ _) ← AlgebraicPreparation.prepare q(∀ x : ℝ, x^2 + Real.pi > 0)
      | throwError "unregistered constant entered the exact algebraic producer"
  unchanged do
    let .error (.unsupported _ _) ← AlgebraicPreparation.prepare q(∀ x : ℝ, 1 / x = 0)
      | throwError "variable denominator entered the exact algebraic producer"
  -- This semantically zero algebraic denominator is not a syntactic a-a
  -- guard. Preparation must retain it; native preflight must reject it.
  unchanged do
    let zero ← checked q(∀ _ : ℝ, 0 / (Real.sqrt 2 * Real.sqrt 2 - 2) = 0)
    unless zero.source.divisors.size == 1 do
      throwError "zero algebraic divisor was erased"
    zero.buildWith (fun _ => none) fun result => do
      let .error .divisor := result
        | throwError "zero algebraic divisor entered native root production"
  unchanged do
    let .none ← FieldRuntime.nonnegative q((-1 : ℝ))
      | throwError "routine nonnegativity proved a negative constant"
  unchanged do
    let .error (.unsupported _ _) ← AlgebraicPreparation.prepare q(∀ x : ℝ, x^2 + Real.sqrt (-1) > 0)
      | throwError "failed radical-base proof did not produce a structured decline"
  let token ← IO.CancelToken.new
  token.set
  let resources : List (String × (Core.Context → Core.Context) × (Exception → Bool)) := [
    ("heartbeat",fun context => {context with maxHeartbeats := 1,initHeartbeats := 0},Exception.isMaxHeartbeat),
    ("recursion",fun context => {context with maxRecDepth := 1,currRecDepth := 1},Exception.isMaxRecDepth),
    ("interruption",fun context => {context with cancelTk? := some token},Exception.isInterrupt)]
  let zero : Q(ℝ) := q(0)
  for (label,limits,expected) in resources do
    unchanged do
      let terminal ← observeTerminal
        (withTheReader Core.Context limits do
          let _ ← FieldRuntime.nonnegative zero
          pure false)
        (fun error => do
          unless expected error do throw error
          pure true)
      unless terminal do throwError "routine nonnegativity swallowed {label}"
  let guarded ← checked q(∀ _ : ℝ, 0 / (Real.sqrt 2 + 1) = 0 ∧ 0 / (Real.sqrt 3 + 1) = 0)
  unless guarded.source.divisors.size == 2 do
    throwError "native preparation erased independent original divisors"
  unless (← isDefEq guarded.source.divisors[0]! q(Real.sqrt 2 + 1)) &&
      (← isDefEq guarded.source.divisors[1]! q(Real.sqrt 3 + 1)) do
    throwError "original divisor source order changed"
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
    constantInput.buildWith registry fun result => do
      let .ok ⟨sources,shared,packet⟩ := result
        | throwError "guard-only prepared source did not produce a native packet"
      let input := packet.family.collection.input
      for quantifier in [RealFormula.Quantifier.existsReal,.forallReal] do
        unless (CompleteReplay.check input.context.codec
            (input.value ∘ GatherCells.values shared (AlgebraicCells.coefficients sources constantInput.indices))
            constantInput.formula ((GatherCells.guards shared (AlgebraicCells.guards sources constantInput.guards)).map input.value)
            packet.radical quantifier packet.rootGraph packet.cells).toOption == some expected do
          throwError "guard-only prepared source changed its checked constant verdict"
  for (target,expected) in [
      (q(∀ x : ℝ, x^2 + Real.sqrt 2 > 0),true),
      (q(∀ x : ℝ, x^2 + Real.sqrt 2 < 0),false)] do
    let algebraic ← checked target
    unless algebraic.source.coefficients.size == 1 && algebraic.source.divisors.isEmpty do
      throwError "irrational coefficient control has the wrong input layout"
    unless ← isDefEq algebraic.source.coefficients[0]! q(Real.sqrt 2) do
      throwError "irrational source coordinate changed"
    algebraic.buildWith (fun _ => none) fun result => do
      let .ok ⟨sources,shared,packet⟩ := result
        | throwError "prepared irrational coefficient did not produce a complete packet"
      let input := packet.family.collection.input
      unless (CompleteReplay.check input.context.codec
          (input.value ∘ GatherCells.values shared (AlgebraicCells.coefficients sources algebraic.indices))
          algebraic.formula [] packet.radical algebraic.quantifier packet.rootGraph packet.cells).toOption == some expected do
        throwError "prepared irrational source changed its quantified verdict"
  addDecl (.thmDecl {
    name := `Hex.RCF.AlgebraicPreparationConformance.runFinished
    levelParams := [], type := mkConst ``True, value := mkConst ``True.intro })
  logInfo "native source identities, ordered irrational and guard-only inputs, aggregate budget and transactional refusals checked"
end Hex.RCF.AlgebraicPreparationConformance
