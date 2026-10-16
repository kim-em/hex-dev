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
  -- These exceptions arrive after actual callback mutations. The observer
  -- shares the state references and cannot restore on production's behalf.
  for interrupted in [false,true] do
    unchanged do
      let name := if interrupted then
        `Hex.RCF.AlgebraicPreparationConformance.interruptMarker
        else `Hex.RCF.AlgebraicPreparationConformance.exceptionMarker
      unless !(← getEnv).contains name do throwError "exception marker already exists"
      let raised ← observeTerminal (do
        let _ ← AlgebraicPreparation.prepare target (fun _ => do
          let _ ← mkFreshExprMVar (mkConst ``Nat)
          let type ← mkEq (mkNatLit 0) (mkNatLit 0)
          addDecl (.thmDecl {name,levelParams := [],type,value := ← mkEqRefl (mkNatLit 0)})
          if interrupted then throwInterruptException
          else throwError "deliberate callback failure")
        pure false) (fun error => do
          if interrupted then
            unless error.isInterrupt do throw error
          else
            match error with
            | .error _ _ => pure ()
            | _ => throw error
          pure true)
      unless raised do throwError "callback exception became a structured return"
      unless !(← getEnv).contains name do throwError "callback exception leaked a declaration"
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
  -- A nonzero coefficient must not be mistaken for the original zero guard.
  unchanged do
    let zero ← checked q(∀ x : ℝ,
      x^2 + Real.sqrt (2 + 0 / (Real.sqrt 2 * Real.sqrt 2 - 2)) > 0)
    unless zero.source.coefficients.size == 1 && zero.source.divisors.size == 1 do
      throwError "mixed zero-divisor source lost a role"
    if hc : 0 < zero.source.coefficients.size then
      if hd : 0 < zero.source.divisors.size then
        let ci : Fin zero.source.coefficients.size := ⟨0,hc⟩
        let di : Fin zero.source.divisors.size := ⟨0,hd⟩
        if zero.coefficients[ci].proposal == 0 || zero.divisors[di].proposal != 0 then
          throwError "mixed zero-divisor control lost its opposite zero statuses"
      else throwError "mixed source has no divisor"
    else throwError "mixed source has no coefficient"
    zero.buildWith (fun _ => none) fun result => do
      let .error .divisor := result
        | throwError "mixed zero divisor was replaced by its nonzero coefficient"
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
  -- Both roles are nonempty and have opposite signs. Swapping a coefficient
  -- for the divisor changes each verdict. The zero numerator preserves the
  -- original guard without creating another irrational generator.
  for (target,expected) in [
      (q(∀ x : ℝ, x^2 + Real.sqrt 2 + 0 / (-1 : ℝ) > 0),true),
      (q(∃ x : ℝ, x^2 + Real.sqrt 2 + 0 / (-1 : ℝ) < 0),false)] do
    let mixed ← checked target
    unless mixed.source.coefficients.size == 1 && mixed.source.divisors.size == 1 do
      throwError "mixed source lost a coefficient or original divisor"
    unless (← isDefEq mixed.source.coefficients[0]! q(Real.sqrt 2)) &&
        (← isDefEq mixed.source.divisors[0]! q((-1 : ℝ))) do
      throwError "mixed source roles changed"
    mixed.buildWith (fun _ => none) fun result => do
      let .ok ⟨sources,shared,packet⟩ := result
        | throwError "mixed prepared source did not produce a complete packet"
      let input := packet.family.collection.input
      unless (CompleteReplay.check input.context.codec
          (input.value ∘ GatherCells.values shared (AlgebraicCells.coefficients sources mixed.indices))
          mixed.formula ((GatherCells.guards shared (AlgebraicCells.guards sources mixed.guards)).map input.value)
          packet.radical mixed.quantifier packet.rootGraph packet.cells).toOption == some expected do
        throwError "mixed coefficient/divisor layout changed the quantified verdict"
  let registry : Q(RealClosure.BaseContext.Registry) := q(fun _ => none)
  for (label, target, guardCount) in #[
      (`rationalAcceptance, q(∀ x : ℝ, x^2 ≥ 0), 0),
      (`algebraicAcceptance, q(∀ x : ℝ, x^2 + Real.sqrt 2 > 0), 0),
      (`falseAcceptance, q(∀ x : ℝ, x^2 + Real.sqrt 2 < 0), 0),
      (`divisorAcceptance, q(∀ x : ℝ, x / (Real.sqrt 2 + 1) = x * (Real.sqrt 2 + 1)⁻¹), 2),
      (`zeroGuardAcceptance, q(∀ _ : ℝ, 0 / (Real.sqrt 2 * Real.sqrt 2 - 2) = 0), 1),
      (`emptyDomainAcceptance, q(∀ x ∈ Set.Ioc (2 : ℝ) 1,
        x + 0 / (Real.sqrt 2 * Real.sqrt 2 - 2) = x), 1),
      (`validEmptyDomainAcceptance, q(∀ x ∈ Set.Ioc (2 : ℝ) 1, x < 0), 0)] do
    let prepared ← checked target
    unless prepared.source.divisors.size == guardCount do
      throwError "source acceptance guard count changed for {label}: {prepared.source.divisors.size}, expected {guardCount}"
    let before := (← getMCtx).decls.toList.length
    let .ok (proof, usage) ← prepared.acceptanceIff target registry
      | throwError "source acceptance equivalence failed: {label}"
    unless (← getMCtx).decls.toList.length == before do
      throwError "successful source acceptance changed caller metavariables"
    let type ← inferType proof
    unless type.isAppOfArity ``Iff 2 do throwError "source acceptance returned no equivalence"
    let domain := mkApp (mkConst ``Fin) (mkNatLit prepared.source.divisors.size)
    let divisors ← FieldLiteral.finiteExpr (mkConst ``Real) prepared.source.divisors q((0 : ℝ))
    let guards ← withLocalDeclD `i domain fun i => do
      mkForallFVars #[i] (← mkAppM ``Ne #[mkApp divisors i, q((0 : ℝ))])
    let expected ← mkAppM ``And #[guards, target]
    let rhs ← instantiateMVars type.getAppArgs[1]!
    unless rhs.isAppOfArity ``And 2 && rhs.getAppArgs[1]! == target do
      throwError "source acceptance changed the exact original goal: {label}"
    -- Numeral instances and binder names can differ in the guard function.
    -- Only that function is compared reducibly; the original target is exact.
    unless ← withTransparency .reducible (isDefEq rhs expected) do
      throwError "source acceptance changed its original divisor conjunction: {label}"
    let lhs := type.getAppArgs[0]!
    unless lhs.isAppOfArity ``AlgebraicCells.accepts 8 do
      throwError "source equivalence does not refer to the actual producer acceptance"
    let info ← getFunInfoNArgs lhs.getAppFn lhs.getAppArgs.size
    let explicit := lhs.getAppArgs.zipIdx |>.filterMap fun (arg, i) =>
      if info.paramInfo[i]!.binderInfo.isExplicit then some arg else none
    unless explicit.size == 6 do throwError "source acceptance has an unexpected arity"
    let generators := explicit[1]!.eta
    let parts := generators.getAppArgs
    unless generators.getAppFn.isConstOf ``Fin.addCases && parts.size >= 2 do
      throwError "source acceptance lost its coefficient/divisor tuple: {← ppExpr generators}"
    let zero : Q(RealAlgebraicNumber) := q(RealAlgebraicNumber.ofRat 0)
    let coefficients ← FieldLiteral.finiteExpr (mkConst ``RealAlgebraicNumber)
      (prepared.coefficients.toArray.map (·.expression)) zero
    let originalDivisors ← FieldLiteral.finiteExpr (mkConst ``RealAlgebraicNumber)
      (prepared.divisors.toArray.map (·.expression)) zero
    unless parts[parts.size-2]! == coefficients && parts.back! == originalDivisors do
      throwError "source acceptance did not use the exact checked algebraic expressions"
    let proposals := prepared.coefficients.map fun entry =>
      {entry with proposal := RealAlgebraicNumber.ofRat 0}
    let divisorProposals := prepared.divisors.map fun entry =>
      {entry with proposal := RealAlgebraicNumber.ofRat 0}
    let edited := {prepared with
      coefficients := proposals
      divisors := divisorProposals
      formula := .not prepared.formula
      quantifier := .existsReal
      usage := usage }
    let .ok (unchangedProof, furtherUsage) ← edited.acceptanceIff target registry
      | throwError "runtime-only edits changed source equivalence"
    unless (← inferType unchangedProof) == type do
      throwError "runtime proposals or runtime syntax entered source acceptance evidence"
    unless furtherUsage.proofNodes > usage.proofNodes && usage.proofNodes > prepared.usage.proofNodes do
      throwError "source acceptance did not return its continued aggregate proof usage"
    let name := `Hex.RCF.AlgebraicPreparationConformance ++ label
    addDecl (.thmDecl {name,levelParams := [],type,value := proof})
    let budget := {prepared.config.ring.budget with proofNodes := usage.proofNodes - 1}
    let ring := {prepared.config.ring with budget}
    let config := {prepared.config with ring}
    let limited := {prepared with config}
    let beforeNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
    unchanged do
      let .error (.budget exhausted) ← limited.acceptanceIff target registry
        | throwError "source acceptance reset its aggregate proof budget"
      unless exhausted.dimension == .proofNodes do throwError "wrong source acceptance exhaustion"
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == beforeNames do
      throwError "exhausted source acceptance leaked auxiliary declarations"
    let budget := {budget with proofNodes := usage.proofNodes}
    let ring := {ring with budget}
    let config := {config with ring}
    let exactLimit := {prepared with config}
    let .ok (_, exactUsage) ← exactLimit.acceptanceIff target registry
      | throwError "source acceptance failed at its exact aggregate proof limit"
    unless exactUsage.proofNodes == usage.proofNodes do
      throwError "source acceptance changed its exact charged proof count"
    let beforeNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
    unchanged do
      let failed ← tryCatchRuntimeEx
        (prepared.acceptanceIff q(True) registry *> pure false) (fun _ => pure true)
      unless failed do throwError "source acceptance ignored its expected original target"
    for (resource, limits, expectedException) in resources do
      unchanged do
        let terminal ← observeTerminal (withTheReader Core.Context limits do
          let _ ← prepared.acceptanceIff target registry
          pure false) (fun error => do
            unless expectedException error do throw error
            pure true)
        unless terminal do throwError "source acceptance swallowed terminal {resource}"
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == beforeNames do
      throwError "terminal source acceptance failure leaked auxiliary declarations"
    if h : 0 < prepared.source.coefficients.size then
      let i : Fin prepared.source.coefficients.size := ⟨0,h⟩
      let entry := prepared.coefficients[i]
      let edited := {entry with identity := q(True.intro)}
      let corrupt := {prepared with coefficients := prepared.coefficients.set i edited}
      unchanged do
        let failed ← tryCatchRuntimeEx (corrupt.acceptanceIff target registry *> pure false) (fun _ => pure true)
        unless failed do throwError "source acceptance trusted an edited coefficient identity"
      unless (← (← getEnv).getLocalConstantInfos).map (·.name) == beforeNames do
        throwError "rejected source acceptance leaked auxiliary declarations"
  withLocalDeclD `c q(ℝ) fun c => do
    let identity ← mkEq c q(Real.sqrt 2)
    withLocalDeclD `identity identity fun identity => do
      let c : Q(ℝ) := c
      let target : Q(Prop) := q(∀ x : ℝ, x^2 + $c > 0)
      let prepared ← checked target
      let .ok (proof, _) ← prepared.acceptanceIff target registry
        | throwError "source acceptance lost the checked local alias"
      let type ← mkForallFVars #[c,identity] (← inferType proof)
      let value ← mkLambdaFVars #[c,identity] proof
      addDecl (.thmDecl {
        name := `Hex.RCF.AlgebraicPreparationConformance.aliasAcceptance
        levelParams := [], type, value })
  logInfo "exact original algebraic producer acceptance, false source, original zero guards, empty domains, aggregate proof budgets and rollback checked"
  addDecl (.thmDecl {
    name := `Hex.RCF.AlgebraicPreparationConformance.runFinished
    levelParams := [], type := mkConst ``True, value := mkConst ``True.intro })
  logInfo "native source identities, ordered irrational and guard-only inputs, aggregate budget and transactional refusals checked"
end Hex.RCF.AlgebraicPreparationConformance
