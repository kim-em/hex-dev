/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.State

@[expose] public section

/-!
# Checked executable package assembly

This module is the supported Mathlib-free assembly boundary for executable
function packages. It joins stable operation and rule declarations, private
package caches, exact callback routes, and the concrete application table for
one checked program. It does not generate offers, choose a policy, mutate a
branch, or grant theorem evidence.

Callbacks may return bounded raw replay quotations. A quotation contains only
its role, package-local schema number, and natural-number body. It deliberately
does not contain a Mathlib proof event. A later companion layer must correlate
each quotation with an accepted runtime transition and a package-owned theorem
schema before it can contribute evidence.

Package callbacks and measure functions are trusted executable configuration
and remain non-preemptible. Decoded programs, bindings, actions, requests,
quotations, and callback results receive no authority from that fact: every
public transition below rechecks their complete structural correspondence.

Here "sealed" means sealed at the ordinary/public import boundary. Lean's
deliberate `import all HexInterval.Executable` exposes private constructors to
trusted source, which is already outside the decoded-runtime threat model. A
repository static check rejects that escape hatch outside an exact reviewed
allowlist.
-/

namespace Hex.Interval.Executable

/-- Logical retained cost supplied by the package which owns the measured
cache or result. These numbers are resource policy, never theorem evidence. -/
structure Cost where
  bytes : Nat := 0
  work : Nat := 0
  deriving DecidableEq, Repr

namespace Cost

def add (left right : Cost) : Cost :=
  { bytes := left.bytes + right.bytes, work := left.work + right.work }

instance : Add Cost := ⟨add⟩

def allowed (bytes work : Nat) (cost : Cost) : Bool :=
  cost.bytes ≤ bytes && cost.work ≤ work

end Cost

/-- The future semantic consumer of one raw quotation. -/
inductive Role where
  | fact
  | equality
  | instance
  deriving DecidableEq, Repr

/-- Complete stable address of one replay representation. -/
structure ReplayKey where
  rule : RuleKey
  role : Role
  schema : Nat
  deriving DecidableEq, Repr

/-- A bounded Mathlib-free replay quotation. It is inert data until a later
companion authenticates its runtime identity and theorem schema. -/
structure Quote where
  role : Role
  schema : Nat
  body : List Nat
  deriving DecidableEq, Repr

/-- One cache-independent representation declared by a handler. The validator
checks encoding shape only; it cannot establish a mathematical proposition. -/
structure ReplayFormat where
  role : Role
  schema : Nat
  validateBody : List Nat → Bool

namespace ReplayFormat

def sameAddress (left right : ReplayFormat) : Bool :=
  left.role == right.role && left.schema == right.schema

def key (rule : RuleKey) (format : ReplayFormat) : ReplayKey :=
  { rule, role := format.role, schema := format.schema }

def accepts (format : ReplayFormat) (quote : Quote) : Bool :=
  format.role == quote.role && format.schema == quote.schema &&
    format.validateBody quote.body

end ReplayFormat

/-- One package result paired with raw, still-untrusted replay quotations. -/
structure Plan (Result : Type) where
  result : Result
  quotes : Array Quote := #[]

/-- A registration resolved against one concrete program node. Structural
inputs and matcher epoch are retained explicitly; the initial compiler emits
only local and scoped applications, for which both fields are empty. -/
structure Application where
  rule : RuleId
  node : NodeId
  kind : ActionKind
  watches : List NodeId
  writes : List NodeId
  structuralInputs : List StructuralInput := []
  matcherEpoch : Option Nat := none
  effort : Nat
  generation : Nat := 0
  deriving Repr

namespace Application

def same (left right : Application) : Bool :=
  left.rule == right.rule && left.node == right.node && left.kind == right.kind &&
    left.watches == right.watches && left.writes == right.writes &&
      left.structuralInputs == right.structuralInputs &&
        left.matcherEpoch == right.matcherEpoch && left.effort == right.effort &&
          left.generation == right.generation

/-- Authenticate every action field owned by one exact application-table row. -/
def accepts (id : ApplicationId) (application : Application) (action : Action) : Bool :=
  action.application == id && action.rule == application.rule &&
    action.node == application.node && action.kind == application.kind &&
      action.inputs.map (·.node) == application.watches &&
        action.writes == application.writes &&
          action.structuralInputs == application.structuralInputs &&
            action.matcherEpoch == application.matcherEpoch &&
              action.effort == application.effort &&
                action.generation == application.generation

end Application

/-- Package-owned logical measures. `metadata` charges the immutable package
declarations, `application` charges each concrete application owned by one of
its handlers, `cache` charges the retained private cache, and `result` charges
one callback result before it is returned. -/
structure Measure (Cache Result : Type) where
  metadata : Cost
  application : Application → Cost
  cache : Cache → Cost
  result : Result → Cost

/-- One registration and the only callback allowed to interpret its rule key. -/
structure Handler (Fact Result Cache : Type) where
  registration : Registration
  /-- Cache-independent applicability check for one exact reconstructed
  application request and its authenticated whole-state snapshot. It may veto
  an offer but cannot choose the compact application identity, route, ports,
  ordering, or theorem schema. The whole snapshot is scheduler data only; the
  invocation callback still receives just its declared fact inputs. -/
  offers : Snapshot Fact → RuleRequest Fact → Bool := fun _ _ => true
  invoke : Cache → RuleRequest Fact → Plan Result × Cache
  /-- Package-owned semantic veto for a structurally valid scoped binding.
  Local registrations do not call this hook. -/
  acceptsScope : Program → ScopeBinding → Bool := fun _ _ => false
  formats : Array ReplayFormat := #[]

/-- An independently assembled executable package with one private cache type. -/
structure Package (Fact Result : Type) where
  Cache : Type
  cache : Cache
  operations : Array Operation := #[]
  requiredOperations : Array Operation := #[]
  handlers : Array (Handler Fact Result Cache)
  measure : Measure Cache Result

/-- Exact route from a flattened rule identifier to its package handler. -/
structure Route where
  package : Nat
  handler : Nat
  deriving DecidableEq, Repr

/-- Every old application, including structural inputs and creation generation,
must remain an exact prefix after an accepted program extension. -/
def applicationsPrefix (before after : Array Application) : Bool := Id.run do
  if after.size < before.size then return false
  for index in [0:before.size] do
    let some old := before[index]? | return false
    let some new := after[index]? | return false
    if !old.same new then return false
  return true

/-- Every old scoped binding remains at the same compact address. -/
def bindingsPrefix (before after : Array ScopeBinding) : Bool := Id.run do
  if after.size < before.size then return false
  for index in [0:before.size] do
    if before[index]? != after[index]? then return false
  return true

/-- Independent assembly and invocation caps. `state` owns structural table
dimensions; the remaining fields bound package-owned logical measurements and
raw quotation encodings. -/
structure Limits where
  state : State.Limits
  maxPackages : Nat
  maxMetadataBytes : Nat
  maxMetadataWork : Nat
  maxCacheBytes : Nat
  maxCacheWork : Nat
  maxResultBytes : Nat
  maxResultWork : Nat
  maxQuotes : Nat
  maxQuoteCells : Nat
  maxAtom : Nat
  maxSchema : Nat
  deriving DecidableEq, Repr

inductive Resource where
  | state (resource : State.Resource)
  | packages
  | metadataBytes
  | metadataWork
  | cacheBytes
  | cacheWork
  | resultBytes
  | resultWork
  | quotes
  | quoteCells
  | atom
  | schema
  deriving DecidableEq, Repr

inductive Error where
  | invalidProgram
  | invalidRegistrations
  | invalidBindings
  | programRejected
  | duplicateOperation (key : OpKey)
  | duplicateRule (key : RuleKey)
  | duplicateFormat (key : ReplayKey)
  | undeclaredHead (rule : RuleKey) (head : OpKey)
  | invalidApplication
  | invalidRequest
  | wrongRoute
  | undeclaredFormat (key : ReplayKey)
  | invalidBody (key : ReplayKey)
  | nonExtension
  | staleGeneration
  | resource (resource : Resource)
  deriving DecidableEq, Repr

/-- One checked registry snapshot. Its constructor is private so routes cannot
be transplanted independently of packages and flattened registrations. -/
structure Registry (Fact Result : Type) where
  private mk ::
  packages : Array (Package Fact Result)
  operations : Array Operation
  registrations : Array Registration
  routes : Array Route
  metadataCost : Cost
  cacheCost : Cost

/-- The sealed correspondence between one program, executable registry, scope
bindings, and concrete application table. -/
structure Assembly (Fact Result : Type) where
  private mk ::
  program : Program
  bindings : Array ScopeBinding
  registry : Registry Fact Result
  applications : Array Application
  /-- Global creation generation, retained even when an extension appends no
  concrete application row. -/
  generation : Nat

/-- A successful callback result retains the exact selected route, owner, and
validated raw quotations. No field is theorem evidence. -/
structure Invocation (Result : Type) where
  private mk ::
  route : Route
  rule : RuleKey
  result : Result
  quotes : Array Quote

private def makeRegistry (packages : Array (Package Fact Result))
    (operations : Array Operation) (registrations : Array Registration)
    (routes : Array Route) (metadataCost cacheCost : Cost) : Registry Fact Result :=
  { packages, operations, registrations, routes, metadataCost, cacheCost }

private def makeAssembly (program : Program) (bindings : Array ScopeBinding)
    (registry : Registry Fact Result) (applications : Array Application)
    (generation : Nat) :
    Assembly Fact Result :=
  { program, bindings, registry, applications, generation }

private def makeInvocation (route : Route) (rule : RuleKey)
    (result : Result) (quotes : Array Quote) : Invocation Result :=
  { route, rule, result, quotes }

private def replacePackage (registry : Registry Fact Result) (index : Nat)
    (package : Package Fact Result) (cacheCost : Cost) : Registry Fact Result :=
  { registry with
    packages := registry.packages.set! index package
    cacheCost }

private def listWithin (limit : Nat) : List α → Bool
  | [] => true
  | _ :: items => limit != 0 && listWithin (limit - 1) items

private def checkProgramLimits (limits : State.Limits) (program : Program) :
    Except Error Unit := do
  if limits.maxOperations < program.operations.size then
    throw (.resource (.state .operations))
  if limits.maxNodes < program.nodes.size then throw (.resource (.state .nodes))
  if program.operations.any (fun operation => !listWithin limits.maxArity operation.inputs) ||
      program.nodes.any (fun node => !listWithin limits.maxArity node.args) then
    throw (.resource (.state .arity))
  let some depths := program.depths? | throw .invalidProgram
  if depths.any (fun depth => limits.maxNodeDepth < depth) then
    throw (.resource (.state .nodeDepth))

private def addOperations : List Operation → Array Operation →
    Except Error (Array Operation)
  | [], operations => pure operations
  | operation :: rest, operations =>
      if operations.any (fun existing => existing.key == operation.key) then
        throw (.duplicateOperation operation.key)
      else
        addOperations rest (operations.push operation)

private def declaresOperation (operations required : Array Operation) (key : OpKey) : Bool :=
  operations.any (fun operation => operation.key == key) ||
    required.any (fun operation => operation.key == key)

private def duplicateFormat? (rule : RuleKey) : List ReplayFormat → Option ReplayKey
  | [] => none
  | format :: formats =>
      if formats.any (fun other => format.sameAddress other) then
        some (format.key rule)
      else
        duplicateFormat? rule formats

private def validateHandlers (operations required : Array Operation) :
    List (Handler Fact Result Cache) → Except Error Unit
  | [] => pure ()
  | handler :: handlers =>
      if !declaresOperation operations required handler.registration.head then
        throw (.undeclaredHead handler.registration.key handler.registration.head)
      else
        match duplicateFormat? handler.registration.key handler.formats.toList with
        | some key => throw (.duplicateFormat key)
        | none => validateHandlers operations required handlers

private def addHandlers (packageIndex : Nat) : Nat →
    List (Handler Fact Result Cache) → Array Registration → Array Route →
      Except Error (Array Registration × Array Route)
  | _, [], registrations, routes => pure (registrations, routes)
  | handlerIndex, handler :: rest, registrations, routes =>
      if registrations.any (fun existing => existing.key == handler.registration.key) then
        throw (.duplicateRule handler.registration.key)
      else
        addHandlers packageIndex (handlerIndex + 1) rest
          (registrations.push handler.registration)
          (routes.push { package := packageIndex, handler := handlerIndex })

private def flatten : Nat → List (Package Fact Result) → Array Operation →
    Array Registration → Array Route →
      Except Error (Array Operation × Array Registration × Array Route)
  | _, [], operations, registrations, routes =>
      pure (operations, registrations, routes)
  | packageIndex, package :: rest, operations, registrations, routes => do
      validateHandlers package.operations package.requiredOperations package.handlers.toList
      let operations ← addOperations package.operations.toList operations
      let (registrations, routes) ←
        addHandlers packageIndex 0 package.handlers.toList registrations routes
      flatten (packageIndex + 1) rest operations registrations routes

private def packagePreflight (limits : Limits) (packages : Array (Package Fact Result)) :
    Except Error (Cost × Cost) := do
  if limits.maxPackages < packages.size then throw (.resource .packages)
  if limits.state.maxRegistryEntries < packages.size then
    throw (.resource (.state .registryEntries))
  let mut operationCount := 0
  let mut ruleCount := 0
  let mut formatCount := 0
  let mut metadataCells := packages.size
  let mut metadataCost : Cost := {}
  let mut cacheCost : Cost := {}
  for package in packages do
    operationCount := operationCount + package.operations.size
    if limits.state.maxOperations < operationCount then
      throw (.resource (.state .operations))
    ruleCount := ruleCount + package.handlers.size
    if limits.state.maxRules < ruleCount then throw (.resource (.state .rules))
    let packageFormats := package.handlers.foldl
      (fun count handler => count + handler.formats.size) 0
    formatCount := formatCount + packageFormats
    if limits.state.maxReplayFormats < formatCount then
      throw (.resource (.state .replayFormats))
    metadataCells := metadataCells + package.operations.size +
      package.requiredOperations.size + package.handlers.size + packageFormats
    if limits.state.maxRegistryEntries < metadataCells then
      throw (.resource (.state .registryEntries))
    if package.operations.any
        (fun operation => !listWithin limits.state.maxArity operation.inputs) ||
        package.requiredOperations.any
          (fun operation => !listWithin limits.state.maxArity operation.inputs) then
      throw (.resource (.state .arity))
    if package.handlers.any (fun handler =>
        handler.registration.binding == .local &&
          (!listWithin (limits.state.maxArity + 1) handler.registration.watches ||
            !listWithin (limits.state.maxArity + 1) handler.registration.writes)) then
      throw (.resource (.state .arity))
    if package.handlers.any (fun handler =>
        handler.registration.binding == .scoped &&
          (!listWithin limits.state.maxScopeNodes handler.registration.watches ||
            !listWithin limits.state.maxScopeNodes handler.registration.writes)) then
      throw (.resource (.state .scopes))
    if package.handlers.any (fun handler =>
        handler.registration.binding == .global &&
          (!listWithin 0 handler.registration.watches ||
            !listWithin 0 handler.registration.writes)) then
      throw (.resource (.state .arity))
    if package.handlers.any (fun handler =>
        limits.state.maxEffort < handler.registration.initialEffort) then
      throw (.resource (.state .effort))
    if package.handlers.any (fun handler =>
        handler.formats.any (fun format => limits.maxSchema < format.schema)) then
      throw (.resource .schema)
    metadataCost := metadataCost + package.measure.metadata
    cacheCost := cacheCost + package.measure.cache package.cache
    if !metadataCost.allowed limits.maxMetadataBytes limits.maxMetadataWork then
      if limits.maxMetadataBytes < metadataCost.bytes then throw (.resource .metadataBytes)
      else throw (.resource .metadataWork)
    if !cacheCost.allowed limits.maxCacheBytes limits.maxCacheWork then
      if limits.maxCacheBytes < cacheCost.bytes then throw (.resource .cacheBytes)
      else throw (.resource .cacheWork)
  pure (metadataCost, cacheCost)

private opaque buildRegistry (limits : Limits) (packages : Array (Package Fact Result)) :
    Except Error (Registry Fact Result) :=
  match packagePreflight limits packages with
  | .error error => .error error
  | .ok (metadataCost, cacheCost) =>
      match flatten 0 packages.toList #[] #[] #[] with
      | .error error => .error error
      | .ok (operations, registrations, routes) =>
          .ok (makeRegistry packages operations registrations routes metadataCost cacheCost)

def operationAccepted (program : Program) (expected : Operation) : Bool :=
  (program.operationWithKey? expected.key).any fun actual =>
    actual.inputs == expected.inputs && actual.output == expected.output

def Registry.acceptsProgram (registry : Registry Fact Result) (program : Program) : Bool :=
  registry.operations.all (operationAccepted program) &&
    registry.packages.all fun package =>
      package.requiredOperations.all (operationAccepted program)

private def Registry.acceptsBinding (registry : Registry Fact Result)
    (program : Program) (binding : ScopeBinding) : Bool :=
  match Registration.find? registry.registrations binding.rule with
  | none => false
  | some (ruleId, registration) =>
      match registry.routes[ruleId.index]? with
      | none => false
      | some route =>
          match registry.packages[route.package]? with
          | none => false
          | some package =>
              match package.handlers[route.handler]? with
              | none => false
              | some handler =>
                  registration.binding == .scoped &&
                    registration.same handler.registration &&
                      ScopeBinding.check program registry.registrations binding &&
                        handler.acceptsScope program binding

private def Registry.acceptsBindings (registry : Registry Fact Result)
    (program : Program) (bindings : Array ScopeBinding) : Bool :=
  ScopeBinding.checkAll program registry.registrations bindings &&
    bindings.all (registry.acceptsBinding program)

private def compileWithin (limit : Nat) (program : Program)
    (rules : Array Registration) (bindings : Array ScopeBinding) (generation : Nat := 0) :
    Except Error (Array Application) := do
  let mut applications := #[]
  for binding in bindings do
    if limit ≤ applications.size then throw (.resource (.state .applications))
    let some (ruleId, rule) := Registration.find? rules binding.rule
      | throw .invalidBindings
    applications := applications.push
      { rule := ruleId, node := binding.anchor, kind := rule.kind
        watches := binding.watches, writes := binding.writes
        effort := rule.initialEffort, generation }
  for nodeIndex in [0:program.nodes.size] do
    let some node := program.nodes[nodeIndex]? | throw .invalidProgram
    let some operation := program.operation? node.op | throw .invalidProgram
    for ruleIndex in [0:rules.size] do
      let some rule := rules[ruleIndex]? | throw .invalidRegistrations
      if rule.binding == .local && rule.head == operation.key then
        if limit ≤ applications.size then throw (.resource (.state .applications))
        let some watches := Slot.resolveAll? { index := nodeIndex } node rule.watches
          | throw .invalidRegistrations
        let some writes := Slot.resolveAll? { index := nodeIndex } node rule.writes
          | throw .invalidRegistrations
        applications := applications.push
          { rule := { index := ruleIndex }, node := { index := nodeIndex }, kind := rule.kind
            watches, writes, effort := rule.initialEffort, generation }
  pure applications

private def compileSuffixWithin (limit start generation : Nat) (program : Program)
    (rules : Array Registration) : Except Error (Array Application) := do
  let mut applications := #[]
  for nodeIndex in [start:program.nodes.size] do
    let some node := program.nodes[nodeIndex]? | throw .invalidProgram
    let some operation := program.operation? node.op | throw .invalidProgram
    for ruleIndex in [0:rules.size] do
      let some rule := rules[ruleIndex]? | throw .invalidRegistrations
      if rule.binding == .local && rule.head == operation.key then
        if limit ≤ applications.size then throw (.resource (.state .applications))
        let some watches := Slot.resolveAll? { index := nodeIndex } node rule.watches
          | throw .invalidRegistrations
        let some writes := Slot.resolveAll? { index := nodeIndex } node rule.writes
          | throw .invalidRegistrations
        applications := applications.push
          { rule := { index := ruleIndex }, node := { index := nodeIndex }, kind := rule.kind
            watches, writes, effort := rule.initialEffort, generation }
  pure applications

private def compileBindingSuffixWithin (limit start generation : Nat)
    (rules : Array Registration) (bindings : Array ScopeBinding) :
    Except Error (Array Application) := do
  let mut applications := #[]
  for index in [start:bindings.size] do
    if limit ≤ applications.size then throw (.resource (.state .applications))
    let some binding := bindings[index]? | throw .invalidBindings
    let some (ruleId, rule) := Registration.find? rules binding.rule
      | throw .invalidBindings
    applications := applications.push
      { rule := ruleId, node := binding.anchor, kind := rule.kind
        watches := binding.watches, writes := binding.writes
        effort := rule.initialEffort, generation }
  pure applications

private def applicationCost (registry : Registry Fact Result)
    (applications : Array Application) : Except Error Cost := do
  let mut cost : Cost := {}
  for index in [0:applications.size] do
    let some application := applications[index]? | throw .invalidApplication
    let some route := registry.routes[application.rule.index]? | throw .wrongRoute
    let some package := registry.packages[route.package]? | throw .wrongRoute
    cost := cost + package.measure.application application
  pure cost

/-- Assemble packages, checked program, scopes, routes, and the initial exact
application table transactionally. Global structural matcher registrations are
retained and routable but deliberately receive no application until a later
matcher-owned structural batch is supported. -/
opaque buildWithin (limits : Limits) (packages : Array (Package Fact Result))
    (program : Program) (bindings : Array ScopeBinding := #[]) :
    Except Error (Assembly Fact Result) :=
  match checkProgramLimits limits.state program with
  | .error error => .error error
  | .ok _ =>
    if !program.check then .error .invalidProgram
    else match buildRegistry limits packages with
      | .error error => .error error
      | .ok registry =>
          if !registry.acceptsProgram program then .error .programRejected
          else if !Registration.check program registry.registrations then
            .error .invalidRegistrations
          else if limits.state.maxApplications < bindings.size then
            .error (.resource (.state .applications))
          else if bindings.any (fun binding =>
              !listWithin limits.state.maxScopeNodes binding.watches ||
                !listWithin limits.state.maxScopeNodes binding.writes) then
            .error (.resource (.state .scopes))
          else if !registry.acceptsBindings program bindings then .error .invalidBindings
          else match compileWithin limits.state.maxApplications program
              registry.registrations bindings with
            | .error error => .error error
            | .ok applications => match applicationCost registry applications with
              | .error error => .error error
              | .ok applicationCost =>
                  let metadataCost := registry.metadataCost + applicationCost
                  if !metadataCost.allowed limits.maxMetadataBytes limits.maxMetadataWork then
                    if limits.maxMetadataBytes < metadataCost.bytes then
                      .error (.resource .metadataBytes)
                    else .error (.resource .metadataWork)
                  else
                    .ok (makeAssembly program bindings { registry with metadataCost } applications 0)

/-- Re-admit every retained executable resource under a possibly tighter
limit before a higher layer invokes a callback. The assembly is already
structurally sealed; this pass rechecks package/cache metadata, program and
application dimensions, and the complete application cost without rebuilding
routes or callback caches. -/
opaque Assembly.preflightWithin (limits : Limits) (assembly : Assembly Fact Result) :
    Except Error Unit := do
  match checkProgramLimits limits.state assembly.program with
  | .error error => throw error
  | .ok _ => pure ⟨⟩
  if limits.state.maxApplications < assembly.bindings.size ||
      limits.state.maxApplications < assembly.applications.size then
    throw (.resource (.state .applications))
  if assembly.bindings.any (fun binding =>
      !listWithin limits.state.maxScopeNodes binding.watches ||
        !listWithin limits.state.maxScopeNodes binding.writes) then
    throw (.resource (.state .scopes))
  let portLimit := Nat.max (limits.state.maxArity + 1) limits.state.maxScopeNodes
  if assembly.applications.any (fun application =>
      !listWithin portLimit application.watches ||
        !listWithin portLimit application.writes) then
    throw (.resource (.state .arity))
  if assembly.applications.any (fun application =>
      !listWithin limits.state.matcherBatchSize application.structuralInputs) then
    throw (.resource (.state .matcherVisits))
  if assembly.applications.any (fun application =>
      limits.state.maxEffort < application.effort) then
    throw (.resource (.state .effort))
  if assembly.applications.any (fun application =>
      limits.state.maxGeneration < application.generation) then
    throw (.resource (.state .generation))
  if limits.state.maxGeneration < assembly.generation then
    throw (.resource (.state .generation))
  let (packageCost, _) ← packagePreflight limits assembly.registry.packages
  let applicationCost ← applicationCost assembly.registry assembly.applications
  let metadataCost := packageCost + applicationCost
  if !metadataCost.allowed limits.maxMetadataBytes limits.maxMetadataWork then
    if limits.maxMetadataBytes < metadataCost.bytes then
      throw (.resource .metadataBytes)
    else throw (.resource .metadataWork)
  pure ()

/-- Extend an assembly by exact append-only program and scoped-binding
suffixes. Old bindings, applications, routes, and caches remain at their
original compact addresses. Fresh scoped applications precede fresh local
node applications in the appended table; their generation must strictly
exceed the retained global assembly generation, including after an extension
which creates no application row. -/
opaque Assembly.extendAllWithin (limits : Limits) (assembly : Assembly Fact Result)
    (program : Program) (bindings : Array ScopeBinding) (generation : Nat) :
    Except Error (Assembly Fact Result) := do
  match assembly.preflightWithin limits with
  | .error error => throw error
  | .ok _ => pure ⟨⟩
  match checkProgramLimits limits.state program with
  | .error error => .error error
  | .ok _ =>
      if !program.check then .error .invalidProgram
      else
        if limits.state.maxApplications < bindings.size ||
            limits.state.maxApplications < assembly.applications.size then
          .error (.resource (.state .applications))
        else if bindings.any (fun binding =>
            !listWithin limits.state.maxScopeNodes binding.watches ||
              !listWithin limits.state.maxScopeNodes binding.writes) then
          .error (.resource (.state .scopes))
        else if !State.programPrefix assembly.program program then .error .nonExtension
        else if !bindingsPrefix assembly.bindings bindings then .error .nonExtension
        else if limits.state.maxGeneration < generation || generation ≤ assembly.generation ||
            assembly.applications.any (fun application => generation ≤ application.generation) then
          .error .staleGeneration
        else if !assembly.registry.acceptsProgram program then .error .programRejected
        else if !Registration.check program assembly.registry.registrations then
          .error .invalidRegistrations
        else if !assembly.registry.acceptsBindings program bindings then
          .error .invalidBindings
        else
          let room := limits.state.maxApplications - assembly.applications.size
          match compileBindingSuffixWithin room assembly.bindings.size generation
              assembly.registry.registrations bindings with
          | .error error => .error error
          | .ok bindingSuffix =>
            let room := room - bindingSuffix.size
            match compileSuffixWithin room assembly.program.nodes.size generation program
                assembly.registry.registrations with
            | .error error => .error error
            | .ok nodeSuffix =>
              let applications := assembly.applications ++ bindingSuffix ++ nodeSuffix
              if !applicationsPrefix assembly.applications applications then .error .nonExtension
              else match applicationCost assembly.registry applications with
                | .error error => .error error
                | .ok applicationCost =>
                    let packageCost := assembly.registry.packages.foldl
                      (fun cost package => cost + package.measure.metadata) (Cost.mk 0 0)
                    let metadataCost := packageCost + applicationCost
                    if !metadataCost.allowed limits.maxMetadataBytes limits.maxMetadataWork then
                      if limits.maxMetadataBytes < metadataCost.bytes then
                        .error (.resource .metadataBytes)
                      else .error (.resource .metadataWork)
                    else
                      .ok (makeAssembly program bindings
                        { assembly.registry with metadataCost } applications generation)

/-- Extend only the program-node suffix and its local applications. Existing
bindings, registry routes, caches, and application rows are retained exactly. -/
opaque Assembly.extendWithin (limits : Limits) (assembly : Assembly Fact Result)
    (program : Program) (generation : Nat) : Except Error (Assembly Fact Result) :=
  assembly.extendAllWithin limits program assembly.bindings generation

private def quoteCells (quotes : Array Quote) : Nat :=
  quotes.foldl (fun total quote => total + quote.body.length) 0

/-- Resolve the immutable replay formats owned by one exact flattened rule.
This projection preserves the sealed route/package/handler correspondence while
letting a theorem companion check format coverage without eliminating the
package's private cache type. -/
opaque Registry.formats? (registry : Registry Fact Result) (rule : RuleId) :
    Option (RuleKey × Array ReplayFormat) :=
  match registry.registrations[rule.index]?, registry.routes[rule.index]? with
  | some registration, some route => match registry.packages[route.package]? with
    | none => none
    | some package => match package.handlers[route.handler]? with
      | none => none
      | some handler =>
          if registration.same handler.registration then
            some (registration.key, handler.formats)
          else none
  | _, _ => none

/-- Count the exact routed replay-format table, failing closed if a supposedly
sealed route can no longer be resolved. -/
opaque Registry.formatCount? (registry : Registry Fact Result) : Option Nat := do
  let mut count := 0
  for index in [0:registry.registrations.size] do
    let (_, formats) ← registry.formats? { index }
    count := count + formats.size
  pure count

private def validateQuotes (limits : Limits) (rule : RuleKey)
    (formats : Array ReplayFormat) (quotes : Array Quote) : Except Error Unit := do
  if limits.maxQuotes < quotes.size then throw (.resource .quotes)
  if limits.maxQuoteCells < quoteCells quotes then throw (.resource .quoteCells)
  for quote in quotes do
    if limits.maxSchema < quote.schema then throw (.resource .schema)
    if quote.body.any (fun atom => limits.maxAtom < atom) then throw (.resource .atom)
    let some format := formats.find? (fun format =>
        format.role == quote.role && format.schema == quote.schema)
      | throw (.undeclaredFormat { rule, role := quote.role, schema := quote.schema })
    if !format.accepts quote then
      throw (.invalidBody { rule, role := quote.role, schema := quote.schema })

private def requestAcceptsChecked (registration : Registration)
    (request : RuleRequest Fact) : Bool :=
  if request.program.programVersion != request.action.programVersion then false
  else match request.program.node? request.action.node with
    | none => false
    | some anchor =>
        let inputNodes := request.inputs.map (fun input => input.node)
        let seen := request.inputs.map fun input =>
          { node := input.node, version := input.version : SeenVersion }
        let common := registration.key == request.action.key &&
          registration.kind == request.action.kind &&
          request.program.operationKey? request.action.node == some registration.head &&
          request.action.inputs == seen && request.action.writes == request.writes &&
          match registration.matchWatch with
          | .none =>
              request.action.structuralInputs.isEmpty && request.action.matcherEpoch.isNone
          | .network =>
              !request.action.structuralInputs.isEmpty && request.action.matcherEpoch.isSome
        common && match registration.binding with
          | .local =>
              Slot.resolveAll? request.action.node anchor registration.watches ==
                  some inputNodes &&
                Slot.resolveAll? request.action.node anchor registration.writes ==
                  some request.writes
          | .scoped =>
              registration.watches.isEmpty && registration.writes.isEmpty &&
                allDistinct inputNodes && allDistinct request.writes &&
                inputNodes.all (fun node => (request.program.node? node).isSome) &&
                request.writes.all (fun node => (request.program.node? node).isSome)
          | .global =>
              registration.watches.isEmpty && registration.writes.isEmpty &&
                inputNodes.isEmpty && request.writes.isEmpty

private def offersChecked [DecidableEq Fact] (assembly : Assembly Fact Result)
    (snapshot : Snapshot Fact) (request : RuleRequest Fact) : Bool :=
  let id := request.action.application
  match assembly.applications[id.index]? with
  | none => false
  | some application =>
      if request.action.rule != application.rule || !application.accepts id request.action then
        false
      else match assembly.registry.registrations[application.rule.index]? with
        | none => false
        | some registration =>
            if !requestAcceptsChecked registration request || request.inputs.any (fun input =>
                snapshot.fact? input.node != some input.fact ||
                  snapshot.version? input.node != some input.version) then false
            else match assembly.registry.routes[application.rule.index]? with
              | none => false
              | some route => match assembly.registry.packages[route.package]? with
                | none => false
                | some package => match package.handlers[route.handler]? with
                  | none => false
                  | some handler =>
                      registration.same handler.registration && handler.offers snapshot request

/-- One sealed, checked snapshot/program context for a complete offer-generation
pass. Its constructor is private so package predicates can be entered through
the cheaper per-application path only after the shared whole-state checks. -/
structure OfferContext (Fact Result : Type) where
  private mk ::
  assembly : Assembly Fact Result
  snapshot : Snapshot Fact
  program : ProgramView

/-- Authenticate the common snapshot and program view once before enumerating
an assembly's applications. Program version remains controller-owned; the
per-request check requires it to agree with each reconstructed action. -/
opaque Assembly.offerContext? [DecidableEq Fact] (assembly : Assembly Fact Result)
    (snapshot : Snapshot Fact) (program : ProgramView) : Option (OfferContext Fact Result) :=
  if !snapshot.check assembly.program ||
      program.operations != assembly.program.operations ||
      program.nodes != assembly.program.nodes ||
      program.generations.size != program.nodes.size ||
      assembly.program.depths? != some program.depths then none
  else some { assembly, snapshot, program }

/-- Ask the exact routed handler whether one reconstructed application is
currently applicable inside an already checked generation pass. The handler
receives the context's authenticated program rather than caller-supplied
program arrays. The predicate is scheduler data only and carries no mutation
or theorem authority. -/
opaque OfferContext.offers [DecidableEq Fact] (context : OfferContext Fact Result)
    (request : RuleRequest Fact) : Bool :=
  offersChecked context.assembly context.snapshot { request with program := context.program }

/-- Execute the exact handler selected by an authenticated application row.
The request must repeat the assembled operation/node program and every
application-owned action field. Program version and generation side tables in
the request's `ProgramView` remain controller-owned snapshot data: this layer
checks their internal request validity but does not claim to own them. Callback
and measure execution are non-preemptible; failure returns no replacement
assembly, so a rejected cache/result/quotation cannot partially commit. -/
opaque Assembly.invokeWithin (limits : Limits) (assembly : Assembly Fact Result)
    (request : RuleRequest Fact) : Except Error (Invocation Result × Assembly Fact Result) := do
  match assembly.preflightWithin limits with
  | .error error => throw error
  | .ok _ => pure ⟨⟩
  if request.program.operations != assembly.program.operations ||
      request.program.nodes != assembly.program.nodes then .error .invalidRequest
  else
    let id := request.action.application
    match assembly.applications[id.index]? with
    | none => .error .invalidApplication
    | some application =>
        if request.action.rule != application.rule then .error .wrongRoute
        else if !application.accepts id request.action then .error .invalidApplication
        else match assembly.registry.registrations[application.rule.index]? with
          | none => .error .wrongRoute
          | some registration =>
              if !RuleRequest.accepts registration request then .error .invalidRequest
              else match assembly.registry.routes[application.rule.index]? with
                | none => .error .wrongRoute
                | some route => match assembly.registry.packages[route.package]? with
                  | none => .error .wrongRoute
                  | some package => match package.handlers[route.handler]? with
                    | none => .error .wrongRoute
                    | some handler =>
                        if !registration.same handler.registration then .error .wrongRoute
                        else
                          let (plan, cache) := handler.invoke package.cache request
                          match validateQuotes limits registration.key handler.formats plan.quotes with
                          | .error error => .error error
                          | .ok _ =>
                              let resultCost := package.measure.result plan.result
                              if !resultCost.allowed limits.maxResultBytes limits.maxResultWork then
                                if limits.maxResultBytes < resultCost.bytes then
                                  .error (.resource .resultBytes)
                                else .error (.resource .resultWork)
                              else
                                let oldCache := package.measure.cache package.cache
                                let newCache := package.measure.cache cache
                                let cacheCost : Cost :=
                                  { bytes := assembly.registry.cacheCost.bytes - oldCache.bytes +
                                      newCache.bytes
                                    work := assembly.registry.cacheCost.work - oldCache.work +
                                      newCache.work }
                                if !cacheCost.allowed limits.maxCacheBytes limits.maxCacheWork then
                                  if limits.maxCacheBytes < cacheCost.bytes then
                                    .error (.resource .cacheBytes)
                                  else .error (.resource .cacheWork)
                                else
                                  let package := { package with cache }
                                  let registry := replacePackage assembly.registry route.package package cacheCost
                                  .ok (makeInvocation route registration.key plan.result plan.quotes,
                                    makeAssembly assembly.program assembly.bindings registry
                                      assembly.applications assembly.generation)

end Hex.Interval.Executable
