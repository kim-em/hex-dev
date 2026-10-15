/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteConditions
public import HexRealClosureTheory.FiniteDependencies
public meta import HexRealClosureTheory.FiniteConditions
public meta import HexRealClosureTheory.FiniteDependencies
public meta import HexRealClosureTheory.FiniteLists

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

/-- Close the advertised proposition and its proof over the same used local
declarations, including declarations needed by their dependent types. -/
private def closeStatement (type proof : Expr) : MetaM (Expr × Expr) := do
  let context ← getLCtx
  let mut used := collectFVars (collectFVars {} type) proof
  for id in context.getFVarIds.reverse do
    if used.fvarSet.contains id then
      let declaration := context.get! id
      used := collectFVars used declaration.type
      if let some value := declaration.value? then used := collectFVars used value
  let locals := context.getFVarIds.filter used.fvarSet.contains |>.map mkFVar
  let closedType ← mkForallFVars locals type (usedLetOnly := false)
  let closedProof ← mkLambdaFVars locals proof (usedLetOnly := false)
  return (closedType, closedProof)

/-- Share a closed mathematical term while retaining its transparent data or
checked proof. These reference-field terms are used for ordinary proofs;
noncomputable interpretations need no native compilation. -/
private def retain (value : Expr) : MetaM Expr := do
  if value.isConst || value.hasFVar then return value
  let type ← inferType value
  let _ ← auditProof value type
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `__finiteWitness)
  let levels := collectLevelParams (collectLevelParams {} type) value |>.params.toList
  let declaration ← if ← isProp type then
      pure (Declaration.thmDecl { name, levelParams := levels, type, value })
    else pure (Declaration.defnDecl {
      name, levelParams := levels, type, value, hints := .regular 0, safety := .safe })
  let options := (← getOptions).setBool `debug.skipKernelTC false
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true))
  return mkConst name (levels.map Lean.Level.param)

/-- The complete joint existential and its ordinary proof. The support and
verified prefixes are retained for inspection; no temporary discovery reader
is a premise of the existential. -/
structure Reconstruction where
  support : Expr
  interpretation : Expr
  prefixes : Array Prefix
  guards : Array Expr
  requested : Array Expr
  type : Expr
  proof : Expr

private def nativeOnly (term : Expr) (readers : Array Expr) : MetaM Unit := do
  if term.hasMVar || term.hasSorry then throwError "incomplete reconstruction input"
  let locals ← getLCtx
  term.forEach fun expression => do
    if let .fvar id := expression then
      unless (locals.find? id).isSome do
        throwError "coefficient support depends on a local discovery hypothesis"
  for reader in readers do
    if term.find? (· == reader) |>.isSome then
      throwError "native support depends on a temporary discovery reader"

private def conjunction (proofs : Array Expr) : MetaM Expr := do
  let mut result := mkConst ``True.intro
  for proof in proofs.reverse do result ← mkAppM ``And.intro #[proof, result]
  return result

/-- Bind actual witnesses against a predicate built with fresh binders.
Checking the instantiated predicate prevents an unrelated proof from being
wrapped in the advertised existential. -/
private partial def witnesses (values : Array Expr) (predicate : Array Expr → MetaM Expr)
    (proof : Expr) : MetaM (Expr × Expr) := go 0 #[]
where
  go (i : Nat) (binders : Array Expr) : MetaM (Expr × Expr) := do
    if let some value := values[i]? then
      withLocalDeclD `witness (← inferType value) fun binder => do
        let (body, obtained) ← go (i + 1) (binders.push binder)
        let abstracted ← mkLambdaFVars #[binder] body
        let instantiated := abstracted.replaceFVars binders (values.extract 0 i)
        let result ← withTransparency .all
          (mkAppOptM ``Exists.intro #[none, some instantiated, some value, some obtained])
        let statement ← mkAppM ``Exists #[abstracted]
        return (statement, result)
    else
      let body ← predicate binders
      let instantiated := body.replaceFVars binders values
      unless ← withTransparency .all (isDefEq (← inferType proof) instantiated) do
        throwError "joint reconstruction proof does not match its witness predicate"
      return (body, proof)

private def pointConditions (levels : Array Prefix) (read : Expr) (points : Array Expr) :
    MetaM (Array Expr) := do
  unless points.size == levels.size do throwError "joint coordinate count changed"
  let mut reader := read
  let mut statements := #[]
  for i in [:levels.size] do
    let some level := levels[i]? | throwError "joint level index changed"
    let point := points[i]!
    statements := statements.push (← mkAppM ``Packing.Inventory.Conditions
      #[level.context, level.entries, level.records, level.facts, reader, point])
    let element ← mkAppM ``Element #[level.context]
    reader ← withLocalDeclD `value element fun value => do
      let polynomial ← mkAppM ``Element.polynomial #[value]
      mkLambdaFVars #[value] (← mkAppM ``Packing.eval #[reader, point, polynomial])
  return statements

private def andStatements (statements : Array Expr) : MetaM Expr := do
  let mut statement := mkConst ``True
  for item in statements.reverse do statement ← mkAppM ``And #[item, statement]
  return statement

/-- Export all coordinates of verified predecessor-ordered prefixes as one
ordinary existential. The first predecessor reader is fixed; every later
reader is evaluation at the preceding coordinate. This also checks the
dependent-coordinate abstraction used by the staged reconstruction driver. -/
def Prefix.joint (levels : Array Prefix) : MetaM (Expr × Expr) := do
  let some first := levels[0]? | throwError "joint prefix export requires a first level"
  let mut obtained := #[]
  for i in [:levels.size] do
    let some level := levels[i]? | throwError "joint prefix index changed"
    if i > 0 then
      let some previous := levels[i - 1]? | throwError "joint predecessor missing"
      unless ← withTransparency .all (isDefEq level.read previous.reader) do
        throwError "joint prefixes are not in predecessor order"
    obtained := obtained.push (← mkAppM ``Packing.Inventory.Data.conditions
      #[level.data, level.zero, level.unit])
  let predicate := fun points => do andStatements (← pointConditions levels first.read points)
  let (statement, proof) ← witnesses (levels.map (·.point)) predicate (← conjunction obtained)
  let (type, proof) ← closeStatement statement proof
  let _ ← auditProof proof type
  kernelCheck `__finitePrefixJoint type proof
  return (type, proof)

/-- Reconstruct saturated native inventories through their validated staged
base history, then choose every algebraic coordinate in predecessor order.
All original arithmetic inputs and the first level's replay support are
collected before the base interpretation is chosen. Remaining guards must
be proved by its finite agreement and the verified prefix suppliers.

Retained lookup proof terms are checked as part of the resulting proof and
are tried before the caller's Boolean decision supplier.

The discovery must include the data and scalar dependencies needed by every
level. Saturation alone is insufficient: missing guards or predecessor keys
cause ordinary proof construction to fail. This consumes an already ordered
native chain; extraction and normalization of live tower contexts are separate.
-/
def reconstruct (base following baseReader : Expr) (discovery : Discovery) (extra : Expr)
    (decisions : Supplier) (statements : Array Expr := #[]) : MetaM Reconstruction := do
  unless discovery.saturated do throwError "unsaturated finite dependencies"
  let levels := discovery.levels
  let temporaryReaders := #[baseReader] ++ levels.flatMap (fun level => #[level.read, level.reader])
  let .app _ coefficient := (← inferType extra) |
    throwError "expected a base coefficient list"
  nativeOnly extra temporaryReaders
  let mut blocks := #[extra]
  for leaf in discovery.leaves do
    if let some coefficients ← leaf.coefficients? then
      nativeOnly coefficients temporaryReaders
      unless ← withTransparency .all (isDefEq (← inferType coefficients) (← inferType extra)) do
        throwError "dependency lowering did not reach the base coefficient carrier"
      blocks := blocks.push coefficients
  let additional ← appendSupport coefficient blocks
  nativeOnly additional temporaryReaders
  let firstSupport ← if let some first := levels[0]? then
      mkAppM ``Packing.Inventory.level #[first.context, first.entries, first.records, first.facts]
    else mkListLit coefficient []
  nativeOnly firstSupport temporaryReaders
  let support ← retain (← mkAppM ``List.append #[firstSupport, additional])
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn "reconstruction: support collected"
      handle.flush
  let existence ← retain (← instantiateMVars
    (← mkAppM ``BaseContext.Context.partial_exists #[base, following, support]))
  let existential ← inferType existence
  unless existential.getAppFn.isConstOf ``Exists do throwError "base bootstrap did not produce an existential"
  let args := existential.getAppArgs
  let interpretation ← retain (← mkAppOptM ``Classical.choose
    #[some args[0]!, some args[1]!, some existence])
  let specification ← mkAppOptM ``Classical.choose_spec #[some args[0]!, some args[1]!, some existence]
  let agreement ← mkAppM ``And.left #[specification]
  let fixed ← mkAppM ``And.right #[specification]
  let closed ← mkAppM ``BaseContext.Context.partialClosed #[base, interpretation]
  let origin ← Base.ofClosed closed
  let agreement ← origin.bindAgreement agreement
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn "reconstruction: guarded base reader constructed"
      handle.flush
  unless ← withTransparency .all (isDefEq (← inferType baseReader) (← inferType origin.read)) do
    throwError "discovery base reader has a different coefficient carrier"
  if let some first := levels[0]? then
    unless ← withTransparency .all (isDefEq first.read baseReader) do
      throwError "first finite level does not follow the base reader"
  -- Share only the deterministic walk of this closed inventory. Every
  -- coefficient proof still checks its original list position and predicate.
  let coefficientCache ← IO.mkRef (none : Option CoefficientWalk)
  let domains := origin.domains (agreementSupplier agreement (some coefficientCache))
  let known ← IO.mkRef discovery.known
  let retained := lookupSupplier known (fun _ => pure none)
  let checks : Supplier := fun type => do
    if type.getAppFn.isConstOf ``Eq && type.getAppArgs[0]!.isConstOf ``Bool then
      if let some proof ← retained type then return some proof
      decisions type
    else pure none
  let baseSupplier := origin.supply domains (fun type => do
    if type.getAppFn.isConstOf ``Eq && type.getAppArgs[0]!.isConstOf ``Bool then
      return ← checks type
    if let some proof ← domains type then return some proof
    checks type)
  let mut supplier := baseSupplier
  let mut verified : Array Prefix := #[]
  let mut conditions := #[agreement, fixed]
  for level in levels do
    for value in #[level.context, level.entries, level.records, level.facts] do nativeOnly value temporaryReaders
    if verified.size > 0 then
      if let some preceding := levels[verified.size - 1]? then
        unless ← withTransparency .all (isDefEq level.read preceding.reader) do
          throwError "finite levels are not in predecessor order"
    let current ← if let some previous := verified.back? then
        previous.extend supplier level.context level.entries level.records level.facts
      else do
        let firstAgreement ← mkAppM ``Transport.Inventory.Agreement.append #[agreement]
        let firstAgreement ← mkAppM ``And.left #[firstAgreement]
        let data ← mkAppM ``Packing.Inventory.level_data
          #[level.context, level.entries, level.records, level.facts,
            origin.read, origin.domain, origin.closed, firstAgreement]
        let zero ← mkAppM ``Transport.Closed.read_zero #[closed]
        let unit ← mkAppM ``Transport.Closed.read_one #[closed]
        Prefix.ofData data zero unit
    conditions := conditions.push (← mkAppM ``Packing.Inventory.Data.conditions
      #[current.data, current.zero, current.unit])
    supplier := current.supplyAll supplier
    verified := verified.push current
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn "reconstruction: ordinary-real prefix constructed"
        handle.flush
  let oldReaders := #[baseReader] ++ levels.flatMap (fun level => #[level.read, level.reader])
  let realReaders := #[origin.read] ++ verified.flatMap (fun level => #[level.read, level.reader])
  let guardScope ← getLCtx
  let guardInstances ← getLocalInstances
  let globalLocals := guardScope.getFVarIds.map mkFVar
  for statement in statements do
    if statement.hasMVar || statement.hasSorry then
      throwError "incomplete requested reconstruction statement"
    unless ← isProp statement do
      throwError "requested reconstruction statement must be a proposition"
  let requestedLeaves := statements.map fun type => (⟨type, guardScope, guardInstances⟩ : Leaf)
  let leaves := discovery.leaves ++ requestedLeaves
  let mut guards : Array Expr := #[]
  let mut requested : Array Expr := #[]
  for index in [:leaves.size] do
    let some leaf := leaves[index]? | throwError "reconstruction guard index changed"
    let (required, guard) ← leaf.withContext do
      -- Abstract the leaf's hypotheses before changing readers, so reader
      -- occurrences in their dependent types are transported as well.
      let hypotheses := (← getLCtx).getFVarIds.filter fun id =>
        (guardScope.find? id).isNone
      let required ← mkForallFVars (hypotheses.map mkFVar) leaf.type (usedOnly := true)
      let required := required.replace fun expression => do
        let i ← oldReaders.findIdx? (· == expression)
        realReaders[i]?
      if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
        IO.FS.withFile path .append fun handle => do
          handle.putStrLn s!"reconstruction: guard {index}/{discovery.leaves.size} {required.getAppFn.constName?} begin"
          handle.flush
      let guard ← withLCtx guardScope guardInstances do
        retain (← build required supplier)
      if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
        IO.FS.withFile path .append fun handle => do
          handle.putStrLn s!"reconstruction: guard {index} built"
          handle.flush
      -- These binders belong to the reconstruction caller. A closed leaf may
      -- have been collected before some of them entered the local context.
      withLCtx guardScope guardInstances do
        let checkedProof ← mkLambdaFVars globalLocals guard
        let checkedType ← mkForallFVars globalLocals required
        let _ ← auditProof checkedProof checkedType
        kernelCheck `__finiteReconstructionGuard checkedType checkedProof
      if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
        IO.FS.withFile path .append fun handle => do
          handle.putStrLn s!"reconstruction: guard {index} kernel checked"
          handle.flush
      return (required, guard)
    guards := guards.push required
    if index ≥ discovery.leaves.size then requested := requested.push required
    conditions := conditions.push guard
  let proof ← conjunction conditions
  let predicate := fun (binders : Array Expr) => do
    let formalInterpretation := binders[0]!
    -- The bootstrap predicate binds its interpretation explicitly. Its proof
    -- may infer types containing the original choice rather than the shared
    -- definition, so replacing the shared term in those types is insufficient.
    let baseConditions ← whnf (mkApp args[1]! formalInterpretation)
    unless baseConditions.getAppFn.isConstOf ``And do
      throwError "base bootstrap predicate changed"
    let mut statements := baseConditions.getAppArgs
    let read ← mkAppM ``BaseContext.Context.partialRead #[base, formalInterpretation]
    let points := binders.extract 1 binders.size
    statements := statements ++ (← pointConditions verified read points)
    let mut formalReaders := #[read]
    let mut previous := read
    for index in [:verified.size] do
      let some level := verified[index]? | throwError "joint guard prefix index changed"
      let element ← mkAppM ``Element #[level.context]
      let current ← withLocalDeclD `value element fun value => do
        let polynomial ← mkAppM ``Element.polynomial #[value]
        mkLambdaFVars #[value] (← mkAppM ``Packing.eval #[previous, points[index]!, polynomial])
      formalReaders := formalReaders ++ #[previous, current]
      previous := current
    for guard in guards do
      statements := statements.push (guard.replace fun expression => do
        let index ← realReaders.findIdx? (· == expression)
        formalReaders[index]?)
    andStatements statements
  let (type, proof) ← witnesses (#[interpretation] ++ verified.map (·.point)) predicate proof
  let (closedType, closedProof) ← closeStatement type proof
  if closedType.find? (· == interpretation) |>.isSome then
    throwError "joint statement retains the chosen base interpretation"
  for point in verified.map (·.point) do
    if closedType.find? (· == point) |>.isSome then
      throwError "joint statement retains a chosen algebraic coordinate"
  for temporary in temporaryReaders do
    if closedType.find? (fun expression => expression == temporary) |>.isSome then
      throwError "joint statement retains a temporary discovery reader"
    if proof.find? (fun expression => expression == temporary) |>.isSome then
      throwError "joint proof retains a temporary discovery reader"
  let _ ← auditProof closedProof closedType
  kernelCheck `__finiteReconstruction closedType closedProof
  return ⟨support, interpretation, verified, guards, requested, closedType, closedProof⟩

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
