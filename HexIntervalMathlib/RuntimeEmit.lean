/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.RuntimeTerminal
public meta import HexIntervalMathlib.RuntimeTerminal

@[expose] public section

/-!
# Kernel-facing quotation of a sealed typed runtime target

This module is the elaborator bridge for the root-target subset of the typed
runtime. Executable callbacks and compiled `Proof.Evidence` values are never
converted into syntax. Instead, packages contribute Meta handles for their
ordinary theorem schemas. A sealed registry checks those handles against the
same package-local schemas used to build `RuntimeProof.Registry`; a checked
root chronology is then quoted as plain `Proof.Event` data and transparently
replayed by `Proof.replayWith`.

There is deliberately no refutation or split emitter here. `Checked.emitWithin`
accepts only a one-node target-terminal tree. Emitter callbacks and quotation
of arbitrary caller facts are pure Lean/Meta callbacks and are not preempted by
these structural limits. Their results are nevertheless rolled back, checked,
and bounded before any expression escapes.
-/

namespace Hex.Interval.RuntimeEmit

open Lean Meta

variable {Fact Cause Plan : Type} {semantics : Proof.Semantics Fact}

/-- One package-owned expression handle for an exact proof schema address. -/
structure Handle where
  key : Proof.Key
  schema : Proof.Emitter Unit

/-- Handles paired with the exact proof package which owns their keys. -/
structure Package (semantics : Proof.Semantics Fact) (Plan : Type := List Nat) where
  proof : Proof.Package semantics Plan
  facts : Array Handle := #[]
  equalities : Array Handle := #[]
  instances : Array Handle := #[]

/-- Registry-wide quotation of the indexed fact domain and its proof laws. -/
structure Quoter (Fact : Type) (semantics : Proof.Semantics Fact) where
  factType : Proof.Emitter Unit
  fact : Proof.Emitter Fact
  semantics : Proof.Emitter Unit
  domain : Proof.Emitter Unit
  laws : Proof.Emitter Unit

structure Limits where
  proof : Proof.Limits
  maxSchemas : Nat
  maxChronology : Nat
  maxExpressionCells : Nat
  deriving DecidableEq, Repr

inductive Resource where
  | schemas
  | chronology
  | expression
  deriving DecidableEq, Repr

inductive Error where
  | proofBuild (error : Proof.BuildError)
  | runtimeProof (error : RuntimeProof.Error)
  | terminal (error : RuntimeTerminal.Error)
  | missingHandle (key : Proof.Key)
  | extraHandle (key : Proof.Key)
  | duplicateHandle (key : Proof.Key)
  | wrongRole (key : Proof.Key)
  | handleKey (key : Proof.Key)
  | proof (error : Proof.Error)
  | malformed
  | emitter
  | replay
  | resource (resource : Resource)
  deriving DecidableEq, Repr

private structure Entry where
  key : Proof.Key
  expr : Lean.Expr

/-- Exact executable/proof/emitter assembly. The private constructor ensures
the emitter view cannot be attached after a runtime registry was built. -/
structure Registry (Fact : Type) (semantics : Proof.Semantics Fact)
    (Cause Plan : Type := List Nat) where
  private mk ::
  runtime : RuntimeProof.Registry Fact semantics Cause Plan
  quoter : Quoter Fact semantics
  packages : Array (Package semantics Plan)

private structure Prepared (Fact : Type) where
  quoteFact : Proof.Emitter Fact
  factType : Lean.Expr
  semanticsExpr : Lean.Expr
  domainExpr : Lean.Expr
  lawsExpr : Lean.Expr
  facts : Array Entry
  equalities : Array Entry
  instances : Array Entry

private def packageKeys (package : Package semantics Plan) (role : Proof.Role) : List Proof.Key :=
  match role with
  | .fact => package.proof.facts.toList.map (·.key)
  | .equality => package.proof.equalities.toList.map (·.key)
  | .instance => package.proof.instances.toList.map (·.key)
  | .refute | .split => []

private def handles (package : Package semantics Plan) (role : Proof.Role) : Array Handle :=
  match role with
  | .fact => package.facts
  | .equality => package.equalities
  | .instance => package.instances
  | .refute | .split => #[]

private def checkPackage (package : Package semantics Plan) (role : Proof.Role) : Except Error Unit := do
  let expected := packageKeys package role
  let actual := (handles package role).toList.map (·.key)
  for handle in handles package role do
    if handle.key.role != role then throw (.wrongRole handle.key)
    if 1 < actual.count handle.key then throw (.duplicateHandle handle.key)
    if !expected.contains handle.key then throw (.extraHandle handle.key)
  for key in expected do
    if !actual.contains key then throw (.missingHandle key)

private def checkPackages (packages : Array (Package semantics Plan)) : Except Error Unit := do
  let mut seen : List Proof.Key := []
  for package in packages do
    for role in [Proof.Role.fact, .equality, .instance] do
      checkPackage package role
      for handle in handles package role do
        if seen.contains handle.key then throw (.duplicateHandle handle.key)
        seen := handle.key :: seen

private def schemaCount (packages : Array (Package semantics Plan)) : Nat :=
  packages.foldl (init := 0) fun count package =>
    count + package.facts.size + package.equalities.size + package.instances.size

private def qRuleKey (value : RuleKey) : MetaM Lean.Expr :=
  mkAppM ``RuleKey.mk #[toExpr value.name, mkNatLit value.schema]

private def qRole : Proof.Role → Lean.Expr
  | .fact => mkConst ``Proof.Role.fact
  | .equality => mkConst ``Proof.Role.equality
  | .instance => mkConst ``Proof.Role.instance
  | .refute => mkConst ``Proof.Role.refute
  | .split => mkConst ``Proof.Role.split

private def qProofKey (value : Proof.Key) : MetaM Lean.Expr := do
  mkAppM ``Proof.Key.mk
    #[← qRuleKey value.rule, qRole value.role, mkNatLit value.bodySchema]

/-- Deterministic syntax-tree size used by `Limits.maxExpressionCells`. -/
def expressionCells : Lean.Expr → Nat
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => 1
  | .app f a => 1 + expressionCells f + expressionCells a
  | .lam _ type body _ | .forallE _ type body _ =>
      1 + expressionCells type + expressionCells body
  | .letE _ type value body _ =>
      1 + expressionCells type + expressionCells value + expressionCells body
  | .mdata _ body | .proj _ _ body => 1 + expressionCells body

private def prepare (emitter : Proof.Emitter Unit) (expected : Lean.Expr) : MetaM (Except Error Lean.Expr) :=
  try
    return .ok (← Proof.emitChecked emitter () expected)
  catch _ =>
    return .error .emitter

private def schemaType (role : Proof.Role) (semanticsExpr : Lean.Expr) : MetaM Lean.Expr :=
  match role with
  | .fact => mkAppM ``Proof.FactSchema #[semanticsExpr]
  | .equality => mkAppM ``Proof.EqualitySchema #[semanticsExpr]
  | .instance => mkAppM ``Proof.InstanceSchema #[semanticsExpr]
  | .refute | .split => throwError "runtime emitter has no terminal schema role"

private def schemaKey (role : Proof.Role) (schema : Lean.Expr) : MetaM Lean.Expr :=
  match role with
  | .fact => mkAppM ``Proof.FactSchema.key #[schema]
  | .equality => mkAppM ``Proof.EqualitySchema.key #[schema]
  | .instance => mkAppM ``Proof.InstanceSchema.key #[schema]
  | .refute | .split => throwError "runtime emitter has no terminal schema role"

private def prepareHandles (limits : Limits) (semanticsExpr : Lean.Expr)
    (packages : Array (Package semantics Plan)) (role : Proof.Role) :
    MetaM (Except Error (Array Entry)) := do
  let expected ← schemaType role semanticsExpr
  let mut entries := #[]
  for package in packages do
    for handle in handles package role do
      let prepared ← prepare handle.schema expected
      match prepared with
      | .error error => return .error error
      | .ok expr =>
          if limits.maxExpressionCells < expressionCells expr then
            return .error (.resource .expression)
          let actualKey ← try
            schemaKey role expr
          catch _ =>
            return .error .emitter
          unless ← isDefEq actualKey (← qProofKey handle.key) do
            return .error (.handleKey handle.key)
          entries := entries.push { key := handle.key, expr }
  return .ok entries

/-- Jointly assemble the exact theorem registry and its package-local syntax
handles. The `RuntimeProof.Registry` is created inside this function; no
prebuilt registry or compatibility key can be spliced onto emitter handles.
Meta callbacks are checked transactionally only when `emitWithin` runs because
the existential theorem registry lives one universe above `MetaM` results. -/
opaque Registry.buildWithin (executableLimits : Executable.Limits)
    (limits : Limits) (key : RuntimeProof.Key)
    (assembly : RuntimeProof.Assembly Fact Cause)
    (quoter : Quoter Fact semantics)
    (packages : Array (Package semantics Plan)) :
    Except Error (Registry Fact semantics Cause Plan) := do
  let _ : ULift.{1} Unit ← match checkPackages packages with
    | .error error => throw error
    | .ok value => pure ⟨value⟩
  let proofPackages := packages.map (·.proof)
  let proof ← Proof.Registry.buildWithin limits.proof assembly.program proofPackages
    |>.mapError Error.proofBuild
  let runtime ← RuntimeProof.Registry.buildWithin executableLimits key assembly proof
    |>.mapError Error.runtimeProof
  pure { runtime := runtime, quoter := quoter, packages := packages }

private def prepareRegistry (limits : Limits)
    (registry : Registry Fact semantics Cause Plan) :
    MetaM (Except Error (Prepared Fact)) := do
  let quoter := registry.quoter
  let packages := registry.packages
  if limits.maxSchemas < schemaCount packages then
    return .error (.resource .schemas)
  let factType ← match ← prepare quoter.factType (mkSort (.succ .zero)) with
    | .error error => return .error error
    | .ok expr => pure expr
  let semanticsType ← mkAppM ``Proof.Semantics #[factType]
  let semanticsExpr ← match ← prepare quoter.semantics semanticsType with
    | .error error => return .error error
    | .ok expr => pure expr
  let domainType ← mkAppM ``Proof.Domain #[semanticsExpr]
  let domainExpr ← match ← prepare quoter.domain domainType with
    | .error error => return .error error
    | .ok expr => pure expr
  let lawsType ← mkAppM ``Proof.Laws #[semanticsExpr]
  let lawsExpr ← match ← prepare quoter.laws lawsType with
    | .error error => return .error error
    | .ok expr => pure expr
  let facts ← match ← prepareHandles limits semanticsExpr packages .fact with
    | .error error => return .error error
    | .ok entries => pure entries
  let equalities ← match ← prepareHandles limits semanticsExpr packages .equality with
    | .error error => return .error error
    | .ok entries => pure entries
  let instances ← match ← prepareHandles limits semanticsExpr packages .instance with
    | .error error => return .error error
    | .ok entries => pure entries
  return .ok
    { quoteFact := quoter.fact
      factType := factType
      semanticsExpr := semanticsExpr
      domainExpr := domainExpr
      lawsExpr := lawsExpr
      facts := facts
      equalities := equalities
      instances := instances }

/-! ## Sealed root-target lineage -/

structure Active (Fact : Type) (semantics : Proof.Semantics Fact) (Cause Plan : Type) where
  private mk ::
  registry : Registry Fact semantics Cause Plan
  terminal : RuntimeTerminal.Active Fact semantics Cause Plan

structure Lineage (Fact : Type) (semantics : Proof.Semantics Fact) (Cause Plan : Type) where
  private mk ::
  registry : Registry Fact semantics Cause Plan
  terminal : RuntimeTerminal.Lineage Fact semantics Cause Plan

structure Checked (Fact : Type) (semantics : Proof.Semantics Fact) (Cause Plan : Type) where
  private mk ::
  registry : Registry Fact semantics Cause Plan
  terminal : RuntimeTerminal.Checked Fact semantics Cause Plan

opaque Active.startWithin [DecidableEq Fact] [DecidableEq Cause]
    (registry : Registry Fact semantics Cause Plan) (input : Proof.Input Fact)
    (controller : Runtime.Controller.State Fact Cause Plan Proof.Key) :
    Except Error (Active Fact semantics Cause Plan) :=
  RuntimeTerminal.Active.startWithin registry.runtime input controller
    |>.map (fun terminal => { registry, terminal })
    |>.mapError Error.terminal

opaque Active.targetWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Search.Result.Limits)
    (measure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (active : Active Fact semantics Cause Plan) (seen : SeenVersion) :
    Except Error (Lineage Fact semantics Cause Plan) :=
  RuntimeTerminal.Active.targetWithin limits measure active.terminal seen
    |>.map (fun terminal => { registry := active.registry, terminal })
    |>.mapError Error.terminal

opaque Lineage.quoteWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : RuntimeProof.Limits)
    (measure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (lineage : Lineage Fact semantics Cause Plan) :
    Except Error (Checked Fact semantics Cause Plan) :=
  RuntimeTerminal.Lineage.quoteWithin limits measure lineage.terminal
    |>.map (fun terminal => { registry := lineage.registry, terminal })
    |>.mapError Error.terminal

/-! ## Plain quotation helpers -/

private def levelOf (type : Lean.Expr) : MetaM Lean.Level := do
  let sort ← whnf (← inferType type)
  match sort with
  | .sort (.succ level) => pure level
  | .sort .zero => throwError "runtime emitter expected a type, not Prop"
  | _ => throwError "runtime emitter expected a type"

private def listExpr (type : Lean.Expr) (items : List Lean.Expr) : MetaM Lean.Expr := do
  let level ← levelOf type
  let nil := mkApp (mkConst ``List.nil [level]) type
  return items.foldr (fun item tail =>
    mkAppN (mkConst ``List.cons [level]) #[type, item, tail]) nil

private def arrayExpr (type : Lean.Expr) (items : Array Lean.Expr) : MetaM Lean.Expr := do
  let level ← levelOf type
  let list ← listExpr type items.toList
  return mkAppN (mkConst ``Array.mk [level]) #[type, list]

private def optionExpr (type : Lean.Expr) (item : Option Lean.Expr) : MetaM Lean.Expr := do
  let level ← levelOf type
  match item with
  | none => return mkApp (mkConst ``Option.none [level]) type
  | some item => return mkAppN (mkConst ``Option.some [level]) #[type, item]

private def qDomain (value : DomainId) : MetaM Lean.Expr :=
  mkAppM ``DomainId.mk #[mkNatLit value.index]

private def qOpKey (value : OpKey) : MetaM Lean.Expr :=
  mkAppM ``OpKey.mk #[toExpr value.name, mkNatLit value.version]

private def qOpId (value : OpId) : MetaM Lean.Expr :=
  mkAppM ``OpId.mk #[mkNatLit value.index]

private def qNodeId (value : NodeId) : MetaM Lean.Expr :=
  mkAppM ``NodeId.mk #[mkNatLit value.index]

private def qRuleId (value : RuleId) : MetaM Lean.Expr :=
  mkAppM ``RuleId.mk #[mkNatLit value.index]

private def qApplicationId (value : ApplicationId) : MetaM Lean.Expr :=
  mkAppM ``ApplicationId.mk #[mkNatLit value.index]

private def qEqualityId (value : EqualityId) : MetaM Lean.Expr :=
  mkAppM ``EqualityId.mk #[mkNatLit value.index]

private def qScope (value : Policy.ScopeId) : MetaM Lean.Expr :=
  mkAppM ``Policy.ScopeId.mk #[mkNatLit value.index]

private def qSeen (value : SeenVersion) : MetaM Lean.Expr := do
  mkAppM ``SeenVersion.mk #[← qNodeId value.node, mkNatLit value.version]

private def qOperation (value : Operation) : MetaM Lean.Expr := do
  let domainType := mkConst ``DomainId
  mkAppM ``Operation.mk #[← qOpKey value.key,
    ← listExpr domainType (← value.inputs.mapM qDomain), ← qDomain value.output]

private def qNode (value : Node) : MetaM Lean.Expr := do
  let nodeType := mkConst ``NodeId
  mkAppM ``Node.mk #[← qDomain value.domain, ← qOpId value.op,
    ← listExpr nodeType (← value.args.mapM qNodeId)]

private def qProgram (value : Program) : MetaM Lean.Expr := do
  mkAppM ``Program.mk
    #[← arrayExpr (mkConst ``Operation) (← value.operations.mapM qOperation),
      ← arrayExpr (mkConst ``Node) (← value.nodes.mapM qNode)]

private def qActionKind : ActionKind → Lean.Expr
  | .forward => mkConst ``ActionKind.forward
  | .backward => mkConst ``ActionKind.backward
  | .improve => mkConst ``ActionKind.improve
  | .shave => mkConst ``ActionKind.shave
  | .instantiate => mkConst ``ActionKind.instantiate
  | .rewrite => mkConst ``ActionKind.rewrite
  | .regularize => mkConst ``ActionKind.regularize
  | .split => mkConst ``ActionKind.split

private def qStructuralKey : StructuralKey → MetaM Lean.Expr
  | .node node => do mkAppM ``StructuralKey.node #[← qNodeId node]
  | .equality equality => do mkAppM ``StructuralKey.equality #[← qEqualityId equality]
  | .application application => do
      mkAppM ``StructuralKey.application #[← qApplicationId application]

private def qStructuralInput (value : StructuralInput) : MetaM Lean.Expr := do
  mkAppM ``StructuralInput.mk #[← qStructuralKey value.key, mkNatLit value.generation]

private def qAction (value : Action) : MetaM Lean.Expr := do
  let seenType := mkConst ``SeenVersion
  let nodeType := mkConst ``NodeId
  let structuralType := mkConst ``StructuralInput
  let natType := mkConst ``Nat
  let epoch ← optionExpr natType (value.matcherEpoch.map mkNatLit)
  mkAppM ``Action.mk
    #[mkNatLit value.serial, mkNatLit value.programVersion,
      ← qApplicationId value.application, ← qRuleId value.rule, ← qRuleKey value.key,
      ← qNodeId value.node, qActionKind value.kind, mkNatLit value.effort,
      mkNatLit value.generation, ← listExpr seenType (← value.inputs.mapM qSeen),
      ← listExpr nodeType (← value.writes.mapM qNodeId),
      ← listExpr structuralType (← value.structuralInputs.mapM qStructuralInput), epoch]

private def qNodeFact (registry : Prepared Fact)
    (value : Proof.NodeFact Fact) : MetaM Lean.Expr := do
  let fact ← Proof.emitChecked registry.quoteFact value.fact registry.factType
  mkAppM ``Proof.NodeFact.mk #[← qNodeId value.node, fact]

private def qInput (registry : Prepared Fact)
    (value : Proof.Input Fact) : MetaM Lean.Expr := do
  let mut facts := #[]
  for fact in value.facts do
    facts := facts.push (← Proof.emitChecked registry.quoteFact fact registry.factType)
  mkAppM ``Proof.Input.mk
    #[← qScope value.scope, ← qProgram value.program,
      ← arrayExpr registry.factType facts, ← qNodeFact registry value.target]

private def qFactStep (registry : Prepared Fact)
    (value : Proof.FactStep Fact) : MetaM Lean.Expr := do
  let fact ← Proof.emitChecked registry.quoteFact value.proposed registry.factType
  let installed ← Proof.emitChecked registry.quoteFact value.installed registry.factType
  mkAppM ``Proof.FactStep.mk
    #[← qScope value.scope, mkNatLit value.programVersion, ← qAction value.action,
      ← qNodeId value.node, ← qSeen value.previous, mkNatLit value.version,
      fact, installed, ← listExpr (mkConst ``SeenVersion) (← value.assumptions.mapM qSeen),
      ← qProofKey value.schema,
      ← listExpr (mkConst ``Nat) (value.body.map mkNatLit)]

private def qEqualityStep (value : Proof.EqualityStep) : MetaM Lean.Expr := do
  mkAppM ``Proof.EqualityStep.mk
    #[← qScope value.scope, mkNatLit value.programVersion, ← qAction value.action,
      ← qEqualityId value.equality, ← qNodeId value.left, ← qNodeId value.right,
      ← listExpr (mkConst ``SeenVersion) (← value.assumptions.mapM qSeen),
      ← qProofKey value.schema,
      ← listExpr (mkConst ``Nat) (value.body.map mkNatLit)]

private def qTransportStep (registry : Prepared Fact)
    (value : Proof.TransportStep Fact) : MetaM Lean.Expr := do
  let installed ← Proof.emitChecked registry.quoteFact value.installed registry.factType
  mkAppM ``Proof.TransportStep.mk
    #[← qScope value.scope, mkNatLit value.programVersion, ← qNodeId value.node,
      ← qSeen value.previous, mkNatLit value.version, ← qEqualityId value.equality,
      ← qSeen value.source, installed]

private def qInstanceStep (value : Proof.InstanceStep) : MetaM Lean.Expr := do
  mkAppM ``Proof.InstanceStep.mk
    #[← qScope value.scope, mkNatLit value.beforeVersion, mkNatLit value.afterVersion,
      ← qAction value.action, ← qProgram value.after,
      ← listExpr (mkConst ``NodeId) (← value.newNodes.mapM qNodeId),
      ← qProofKey value.schema,
      ← listExpr (mkConst ``Nat) (value.body.map mkNatLit)]

private def qEvent (registry : Prepared Fact) :
    Proof.Event Fact → MetaM Lean.Expr
  | .fact step => do
      pure (mkAppN (mkConst ``Proof.Event.fact)
        #[registry.factType, ← qFactStep registry step])
  | .equality step => do
      pure (mkAppN (mkConst ``Proof.Event.equality)
        #[registry.factType, ← qEqualityStep step])
  | .transport step => do
      pure (mkAppN (mkConst ``Proof.Event.transport)
        #[registry.factType, ← qTransportStep registry step])
  | .instance step => do
      pure (mkAppN (mkConst ``Proof.Event.instance)
        #[registry.factType, ← qInstanceStep step])

private def qRegistration (value : Registration) : MetaM Lean.Expr := do
  let qSlot : Slot → MetaM Lean.Expr
    | .result => pure (mkConst ``Slot.result)
    | .argument index => mkAppM ``Slot.argument #[mkNatLit index]
  let qBinding : BindingKind → Lean.Expr
    | .local => mkConst ``BindingKind.local
    | .scoped => mkConst ``BindingKind.scoped
    | .global => mkConst ``BindingKind.global
  let qWatch : MatchWatch → Lean.Expr
    | .none => mkConst ``MatchWatch.none
    | .network => mkConst ``MatchWatch.network
  mkAppM ``Registration.mk
    #[← qRuleKey value.key, ← qOpKey value.head, qActionKind value.kind,
      ← listExpr (mkConst ``Slot) (← value.watches.mapM qSlot),
      ← listExpr (mkConst ``Slot) (← value.writes.mapM qSlot),
      qBinding value.binding, toExpr value.watchesProgram, qWatch value.matchWatch,
      mkNatLit value.initialEffort]

private def qEntries (type : Lean.Expr) (entries : Array Entry) : MetaM Lean.Expr :=
  arrayExpr type (entries.map (·.expr))

private def qResolver (runtime : RuntimeProof.Registry Fact semantics Cause Plan)
    (registry : Prepared Fact) : MetaM Lean.Expr := do
  let registrations ← arrayExpr (mkConst ``Registration)
    (← runtime.proof.registrations.mapM qRegistration)
  let factType ← mkAppM ``Proof.FactSchema #[registry.semanticsExpr]
  let equalityType ← mkAppM ``Proof.EqualitySchema #[registry.semanticsExpr]
  let instanceType ← mkAppM ``Proof.InstanceSchema #[registry.semanticsExpr]
  mkAppM ``Proof.Resolver.mk
    #[registrations, ← qEntries factType registry.facts,
      ← qEntries equalityType registry.equalities,
      ← qEntries instanceType registry.instances]

private def qLimits (value : Proof.Limits) : MetaM Lean.Expr :=
  mkAppM ``Proof.Limits.mk
    #[mkNatLit value.maxPackages, mkNatLit value.maxSchemas,
      mkNatLit value.maxBodyCells, mkNatLit value.maxDependencies,
      mkNatLit value.maxChronology]

/-- Extract the ordinary Evidence term from a transparently successful replay.
The success proof is generated and kernel-checked from the quoted plain data. -/
def evidenceOfReplay {claim : Prop} (result : Except Proof.Error (Proof.Evidence claim))
    (success : result.toOption.isSome = true) : Proof.Evidence claim :=
  result.toOption.get success

private def eventWithin (limits : Limits) : Proof.Event Fact → Except Error Unit
  | .fact step => do
      Proof.bodyCheck limits.proof step.schema .fact step.body |>.mapError Error.proof
      Proof.dependenciesCheck limits.proof step.assumptions |>.mapError Error.proof
  | .equality step => do
      Proof.bodyCheck limits.proof step.schema .equality step.body |>.mapError Error.proof
      Proof.dependenciesCheck limits.proof step.assumptions |>.mapError Error.proof
  | .transport _ => pure ()
  | .instance step =>
      Proof.bodyCheck limits.proof step.schema .instance step.body |>.mapError Error.proof

private def restoreClean (saved : Lean.Meta.SavedState) : MetaM Unit := do
  saved.restore
  Lean.Meta.resetCache
  modifyThe Lean.Core.State fun state => { state with cache := {} }

/-- The exact quoted proof input and its correlated evidence expression. The
private constructor prevents callers from pairing independently emitted terms. -/
structure Emitted where
  private mk ::
  input : Lean.Expr
  evidence : Lean.Expr

/-- Emit one exact input/evidence pair from a sealed one-node target lineage.
Neither expression is returned until every callback, resource check,
transparent reduction, `Meta.check`, and exact type comparison has succeeded.
Both expressions are bounded independently by `maxExpressionCells`. -/
opaque Checked.emitResultWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (checked : Checked Fact semantics Cause Plan) :
    MetaM (Except Error Emitted) := do
  let tree := checked.terminal.bundle.tree
  let recipe := checked.terminal.bundle.recipe
  if tree.nodes.size != 1 || recipe.events.size != 1 || recipe.edges.size != 1 then
    return .error .malformed
  let some node := tree.nodes[0]? | return .error .malformed
  let some events := recipe.events[0]? | return .error .malformed
  let some edge := recipe.edges[0]? | return .error .malformed
  if edge.parent.isSome || edge.side.isSome || edge.seed.isSome then return .error .malformed
  let (source, result) ← match node with
    | .terminal source (.target target) => pure (source, target.seen)
    | .pending _ | .terminal _ (.unknown _) | .terminal _ (.refute _) | .split .. =>
        return .error .malformed
  if limits.maxChronology < events.length then return .error (.resource .chronology)
  for event in events do
    match eventWithin limits event with
    | .error error => return .error error
    | .ok _ => pure ()
  let run (_ : Unit) : MetaM (Except Error Emitted) := do
    let prepared ← match ← prepareRegistry limits checked.registry with
      | .error error => return .error error
      | .ok prepared => pure prepared
    let inputExpr ← qInput prepared checked.terminal.input
    if limits.maxExpressionCells < expressionCells inputExpr then
      return .error (.resource .expression)
    let inputType ← mkAppM ``Proof.Input #[prepared.factType]
    let emitter : Proof.Emitter Lean.Expr := { emit := pure }
    let inputExpr ← Proof.emitChecked emitter inputExpr inputType
    let resolverExpr ← qResolver checked.registry.runtime prepared
    let mut eventExprs := []
    for event in events do eventExprs := eventExprs.concat (← qEvent prepared event)
    let eventsExpr ← listExpr (← mkAppM ``Proof.Event #[prepared.factType]) eventExprs
    let replay ← mkAppM ``Proof.replayWith
      #[← qLimits limits.proof, resolverExpr, prepared.domainExpr,
        prepared.lawsExpr, inputExpr, eventsExpr,
        mkNatLit source.branch.programVersion, ← qProgram source.branch.program, ← qSeen result]
    let option ← mkAppM ``Except.toOption #[replay]
    let ready ← mkAppM ``Option.isSome #[option]
    let success ← mkDecideProof (← mkAppM ``Eq #[ready, toExpr true])
    let candidate ← mkAppM ``evidenceOfReplay #[replay, success]
    if limits.maxExpressionCells < expressionCells candidate then
      return .error (.resource .expression)
    let program ← mkAppM ``Proof.Input.program #[inputExpr]
    let base ← mkAppM ``Proof.initialBase #[inputExpr]
    let target ← mkAppM ``Proof.Input.target #[inputExpr]
    let claim ← mkAppM ``Proof.Semantics.Entails
      #[prepared.semanticsExpr, program, base, target]
    let expected ← mkAppM ``Proof.Evidence #[claim]
    let evidence ← Proof.emitChecked emitter candidate expected
    return .ok { input := inputExpr, evidence }
  let saved ← Lean.Meta.saveState
  let result ← try
    run ()
  catch _ =>
    pure (.error .replay)
  restoreClean saved
  return result

/-- Compatibility projection for callers which need only the evidence term.
Unlike `emitResultWithin`, this discards the quoted input which indexes that
term. A caller using the result to discharge a pre-existing claim must pin its
claim input first (for example by exact definitional comparison with
`emitResultWithin.input`); successful emission alone authenticates only the
claim indexed by the quoter-produced input term. -/
def Checked.emitWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (checked : Checked Fact semantics Cause Plan) :
    MetaM (Except Error Lean.Expr) := do
  match ← checked.emitResultWithin limits with
  | .error error => return .error error
  | .ok emitted => return .ok emitted.evidence

end Hex.Interval.RuntimeEmit
