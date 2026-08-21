/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PayloadArena

@[expose] public section

/-!
# Extensible propagator packages

This module assembles independently defined function packages without adding
function semantics to the interval engine.  A package existentially owns one
private cache type shared by all of its handlers.  The compiled registry
flattens only operation signatures and registrations for the engine and keeps
an opaque route back to the selected package callback.

The registry itself is the arbitrary cache threaded by `Propagator.drive` or
the external policy driver.  Updating a package cache cannot alter its stable
operations, registrations, callbacks, routes, or start checks.  Package caches
are performance state only: for the same request and logical budget, cache
contents must not change the callback's observable outcome.  Semantic state
instead needs an explicit versioned dependency and wakeup protocol. Immutable
proof-payload drafts travel beside the outcome; a session layer must freeze
them in a separate per-run arena before their identifiers enter engine
provenance. Each handler also owns cache-independent replay formats. Their
validators check bounded representation shape without adding any arithmetic
or function case split to the generic registry.
-/

namespace Hex.Interval.Experiment.Propagator

/-- One package-produced result before its reply-local proof labels are frozen
into the run's immutable arena. -/
structure Plan (Fact : Type) where
  outcome : Outcome Fact
  drafts : List PayloadArena.Draft

/-- One cache-independent replay representation local to the owning handler's
exact `RuleKey` compatibility epoch.  Its numeric schema is a recipe variant
inside that epoch.  The validator is called only after generic arena preflight
has bounded the draft and its body. It checks representation shape, not
mathematical soundness. -/
structure ReplayFormat where
  role : PayloadArena.Role
  schema : Nat
  validateBody : List Nat -> Bool

namespace ReplayFormat

def sameAddress (left right : ReplayFormat) : Bool :=
  left.role == right.role && left.schema == right.schema

def replayKey (rule : RuleKey) (format : ReplayFormat) :
    PayloadArena.ReplayKey :=
  { rule, role := format.role, schema := format.schema }

end ReplayFormat

/-- Immutable replay metadata selected together with one handler invocation.
`rule` plus a format's role and numeric schema is the complete dispatch key. -/
structure ReplaySnapshot where
  private mk ::
  rule : RuleKey
  formats : Array ReplayFormat

private def makeReplay (rule : RuleKey)
    (formats : Array ReplayFormat) : ReplaySnapshot :=
  { rule, formats }

namespace ReplaySnapshot

def validateDraft (snapshot : ReplaySnapshot) (draft : PayloadArena.Draft) :
    Option PayloadArena.Invalid :=
  let key := draft.replayKey snapshot.rule
  match snapshot.formats.find?
      (fun format => format.role == draft.role && format.schema == draft.schema) with
  | none => some (.undeclaredFormat key)
  | some format =>
      if format.validateBody draft.body then none else some (.invalidBody key)

/-- Freeze one plan through the rule owner and body validators carried by this
single immutable snapshot. Proof-producing sessions use this paired operation
instead of independently supplying an owner and validator. -/
def freeze (snapshot : ReplaySnapshot) (limits : PayloadArena.Limits)
    (arena : PayloadArena.Arena) (origin : Action)
    (outcome : Outcome Fact) (drafts : List PayloadArena.Draft) :
    PayloadArena.Result Fact :=
  PayloadArena.freezeChecked limits arena origin snapshot.rule
    snapshot.validateDraft outcome drafts

end ReplaySnapshot

/-- A package plan paired with the immutable replay metadata of the exact
handler that produced it. -/
structure Invocation (Fact : Type) where
  private mk ::
  plan : Plan Fact
  replay : ReplaySnapshot

private def makeInvocation (plan : Plan Fact)
    (replay : ReplaySnapshot) : Invocation Fact :=
  { plan, replay }

/-- The callback shape shared by direct and session-owned drivers. -/
abbrev Invoke (Fact Cache : Type) :=
  Cache -> RuleRequest Fact -> Plan Fact × Cache

/-- Compatibility shape for a callback that produces no immutable evidence.
Every candidate carries a payload identifier, so a handler lifted through a
dropping-drafts constructor cannot contribute candidates through a
proof-producing session: `PayloadArena.freeze` requires a matching draft for
every payload use, while this callback shape supplies none. -/
abbrev BareInvoke (Fact Cache : Type) :=
  Cache -> RuleRequest Fact -> Outcome Fact × Cache

/-- One registration and the only callback allowed to interpret its key. -/
structure Handler (Fact Cache : Type) where
  registration : Registration
  invoke : Invoke Fact Cache
  /-- Package-owned semantic preflight for one concrete scoped application.
  Local registrations never call this hook.  The default is fail-closed.  A
  checked session passes `Registry.acceptsBinding registry` to `Engine.start`,
  preserving the same package veto for dynamically proposed scopes. -/
  acceptsScope : Program -> ScopeBinding -> Bool := fun _ _ => false
  /-- Immutable cache-independent replay representations owned by this rule. -/
  replayFormats : Array ReplayFormat := #[]

namespace Handler

/-- Lift a callback with no payload drafts into the planned protocol.
The explicit name prevents proof-producing packages from choosing this
evidence-discarding compatibility path by accident. -/
def bareDroppingDrafts (registration : Registration)
    (invoke : BareInvoke Fact Cache) : Handler Fact Cache :=
  { registration
    invoke := fun cache request =>
      let (outcome, cache) := invoke cache request
      ({ outcome, drafts := [] }, cache) }

/-- Lift a cache-independent callback while producing no proof drafts. -/
def readOnlyDroppingDrafts (registration : Registration)
    (invoke : RuleRequest Fact -> Outcome Fact) : Handler Fact Cache :=
  bareDroppingDrafts registration fun cache request => (invoke request, cache)

/-- A cache-independent handler which produces no proof drafts. -/
def statelessDroppingDrafts (registration : Registration)
    (invoke : RuleRequest Fact -> Outcome Fact) : Handler Fact Unit :=
  readOnlyDroppingDrafts registration invoke

/-- A cache-independent callback that returns complete reply-local evidence. -/
def readOnlyPlanned (registration : Registration)
    (invoke : RuleRequest Fact -> Plan Fact)
    (replayFormats : Array ReplayFormat := #[]) : Handler Fact Cache :=
  { registration, replayFormats
    invoke := fun cache request => (invoke request, cache) }

/-- A stateless callback that returns complete reply-local evidence. -/
def statelessPlanned (registration : Registration)
    (invoke : RuleRequest Fact -> Plan Fact)
    (replayFormats : Array ReplayFormat := #[]) : Handler Fact Unit :=
  readOnlyPlanned registration invoke replayFormats

end Handler

/-- An independently upgradeable collection of operations and handlers.

All handlers in one package share `Cache`; different packages in the same
registry may choose unrelated cache types.  `operations` contains signatures
introduced by this package, while `requiredOperations` records exact
signatures supplied elsewhere but interpreted by its matchers.  A handler may
target such an external operation; final head validation remains the engine's
responsibility once the complete program is available.  `acceptsLimits` is a
package-owned configuration preflight over the engine and payload-arena
envelopes, not a soundness boundary: every reply is still checked by both
owners. -/
structure Package (Fact : Type) where
  Cache : Type
  cache : Cache
  operations : Array Operation := #[]
  requiredOperations : Array Operation := #[]
  handlers : Array (Handler Fact Cache)
  acceptsLimits : Program -> Limits -> PayloadArena.Limits -> Bool :=
    fun _ _ _ => true
  /-- Non-semantic routing telemetry used to check that only the selected
  package snapshot changes. -/
  invocations : Nat := 0

/-- Compact dispatch address into an existential package and its homogeneous
handler table. -/
structure Route where
  package : Nat
  handler : Nat
  deriving DecidableEq, Repr

/-- One compiled, stateful registry snapshot.  The three flattened arrays are
immutable after assembly; invocation updates only one existential package's
cache and non-semantic invocation counter. -/
structure Registry (Fact : Type) where
  private mk ::
  packages : Array (Package Fact)
  operations : Array Operation
  registrations : Array Registration
  routes : Array Route

/- Stable opaque diagnostic codes for failures before a package callback is
entered. -/
namespace DispatchCode

def missingRoute : Nat := 240
def missingRegistration : Nat := 241
def missingPackage : Nat := 242
def missingHandler : Nat := 243
def registryMismatch : Nat := 244
def requestMismatch : Nat := 245

end DispatchCode

private def makeRegistry (packages : Array (Package Fact))
    (operations : Array Operation) (registrations : Array Registration)
    (routes : Array Route) : Registry Fact :=
  { packages, operations, registrations, routes }

private def replacePackage (registry : Registry Fact) (index : Nat)
    (package : Package Fact) : Registry Fact :=
  { registry with packages := registry.packages.set! index package }

/-- Failure while flattening independently supplied packages. -/
inductive RegistryError where
  | duplicateOperation (key : OpKey)
  | duplicateRule (key : RuleKey)
  | duplicateFormat (key : PayloadArena.ReplayKey)
  | undeclaredHead (rule : RuleKey) (head : OpKey)
  | resourceLimit (resource : Resource)
  deriving DecidableEq, Repr

namespace Registry

def addOperations : List Operation -> Array Operation ->
    Except RegistryError (Array Operation)
  | [], operations => pure operations
  | operation :: rest, operations =>
      if operations.any (fun existing => existing.key == operation.key) then
        throw (.duplicateOperation operation.key)
      else
        addOperations rest (operations.push operation)

def declaresOperation (operations required : Array Operation) (key : OpKey) : Bool :=
  operations.any (fun operation => operation.key == key) ||
    required.any (fun operation => operation.key == key)

def duplicateFormat? (rule : RuleKey) :
    List ReplayFormat -> Option PayloadArena.ReplayKey
  | [] => none
  | format :: formats =>
      if formats.any (fun other => format.sameAddress other) then
        some (format.replayKey rule)
      else
        duplicateFormat? rule formats

def validateHandlers (operations required : Array Operation) :
    List (Handler Fact Cache) -> Except RegistryError Unit
  | [] => pure ()
  | handler :: handlers =>
      if !declaresOperation operations required handler.registration.head then
        throw (.undeclaredHead handler.registration.key handler.registration.head)
      else
        match duplicateFormat? handler.registration.key
            handler.replayFormats.toList with
        | some key => throw (.duplicateFormat key)
        | none => validateHandlers operations required handlers

def addHandlers (packageIndex : Nat) : Nat -> List (Handler Fact Cache) ->
    Array Registration -> Array Route ->
      Except RegistryError (Array Registration × Array Route)
  | _, [], registrations, routes => pure (registrations, routes)
  | handlerIndex, handler :: rest, registrations, routes =>
      if registrations.any
          (fun existing => existing.key == handler.registration.key) then
        throw (.duplicateRule handler.registration.key)
      else
        addHandlers packageIndex (handlerIndex + 1) rest
          (registrations.push handler.registration)
          (routes.push { package := packageIndex, handler := handlerIndex })

def flatten : Nat -> List (Package Fact) -> Array Operation ->
    Array Registration -> Array Route ->
      Except RegistryError (Array Operation × Array Registration × Array Route)
  | _, [], operations, registrations, routes =>
      pure (operations, registrations, routes)
  | packageIndex, package :: rest, operations, registrations, routes => do
      validateHandlers package.operations package.requiredOperations
        package.handlers.toList
      let operations <- addOperations package.operations.toList operations
      let (registrations, routes) <-
        addHandlers packageIndex 0 package.handlers.toList registrations routes
      flatten (packageIndex + 1) rest operations registrations routes

def preflight (limits : Limits) (packages : Array (Package Fact)) :
    Except RegistryError Unit := do
  if limits.maxRegistryEntries < packages.size then
    throw (.resourceLimit .registryEntries)
  let mut operationCount := 0
  let mut ruleCount := 0
  let mut replayFormatCount := 0
  let mut metadataCount := 0
  for package in packages do
    operationCount := operationCount + package.operations.size
    ruleCount := ruleCount + package.handlers.size
    if limits.maxOperations < operationCount then
      throw (.resourceLimit .operations)
    if limits.maxRules < ruleCount then
      throw (.resourceLimit .rules)
    let packageFormatCount :=
      package.handlers.foldl
        (fun count handler => count + handler.replayFormats.size) 0
    replayFormatCount := replayFormatCount + packageFormatCount
    if limits.maxReplayFormats < replayFormatCount then
      throw (.resourceLimit .replayFormats)
    metadataCount := metadataCount + package.operations.size +
      package.requiredOperations.size + package.handlers.size + packageFormatCount
    if limits.maxRegistryEntries < metadataCount then
      throw (.resourceLimit .registryEntries)
    if package.operations.any
        (fun operation => !listWithin limits.maxArity operation.inputs) ||
        package.requiredOperations.any
          (fun operation => !listWithin limits.maxArity operation.inputs) ||
        package.handlers.any (fun handler =>
          !listWithin (limits.maxArity + 1) handler.registration.watches ||
            !listWithin (limits.maxArity + 1) handler.registration.writes) then
      throw (.resourceLimit .arity)

/-- Resource-preflight package metadata before duplicate scans or flattened
array allocation. Dedicated caps bound total metadata and replay-format
declarations without borrowing executable operation headroom. Assembly order
is package-major and then handler-major; exact operation and rule keys are
unique in the snapshot. -/
opaque buildWithin (limits : Limits) (packages : Array (Package Fact)) :
    Except RegistryError (Registry Fact) :=
  match preflight limits packages with
  | .error error => .error error
  | .ok () =>
      match flatten 0 packages.toList #[] #[] #[] with
      | .error error => .error error
      | .ok (operations, registrations, routes) =>
          .ok (makeRegistry packages operations registrations routes)

/-- Resolve a contributed signature by stable key.  The returned value carries
no `OpId`: compact identifiers belong to the final frontend program, whose
operation order may differ from package assembly order. -/
def operation? (registry : Registry Fact) (key : OpKey) : Option Operation :=
  registry.operations.toList.find? fun operation => operation.key == key

def operationAccepted (program : Program) (expected : Operation) : Bool :=
  (program.operationWithKey? expected.key).any fun actual =>
    actual.inputs == expected.inputs && actual.output == expected.output

/-- A frontend may add operations of its own, but every package-owned key must
retain the exact domain signature under which its handlers were assembled.
External signatures explicitly required by a package are checked as well. -/
def acceptsProgram (registry : Registry Fact) (program : Program) : Bool :=
  registry.operations.all (operationAccepted program) &&
    registry.packages.all fun package =>
      package.requiredOperations.all (operationAccepted program)

/-- Run every package-owned configuration preflight over the final program,
engine resource envelope, and proof-payload arena envelope. -/
def acceptsLimits (registry : Registry Fact) (program : Program)
    (limits : Limits) (arenaLimits : PayloadArena.Limits) : Bool :=
  DispatchCode.requestMismatch ≤ limits.maxDiagnosticValue &&
    registry.packages.all fun package =>
      package.acceptsLimits program limits arenaLimits

end Registry

namespace Registry

/-- Route a structurally valid start-time scope back to the package which owns
its rule and ask that package to accept the semantic binding. -/
def acceptsBinding (registry : Registry Fact) (program : Program)
    (binding : ScopeBinding) : Bool :=
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

/-- Check a complete start-time binding table after assembling the final
package registry and program.  Passing `Registry.acceptsBinding registry` to
`Engine.start` also installs this check for dynamic admission; the engine still
repeats its independent structural validation at its own boundary. -/
def acceptsBindings (registry : Registry Fact) (program : Program)
    (bindings : Array ScopeBinding) : Bool :=
  ScopeBinding.checkAll program registry.registrations bindings &&
    bindings.all (registry.acceptsBinding program)

/-- A negative plan for a dispatch failure before any callback or replay
format can be selected. -/
private def failedInvocation (rule : RuleKey) (code : Nat) : Invocation Fact :=
  makeInvocation
    { outcome := .failed code, drafts := [] }
    (makeReplay rule #[])

/-- Route one engine-owned rule identifier to its package callback and retain
its reply-local proof drafts together with that handler's replay formats.
Dispatch uses compact validated indices; it never branches on the semantic
operation or rule key. Only the selected package cache is replaced. -/
opaque invokePlanned (registry : Registry Fact) (request : RuleRequest Fact) :
    Invocation Fact × Registry Fact :=
  match registry.routes[request.action.rule.index]? with
  | none =>
      (failedInvocation request.action.key DispatchCode.missingRoute, registry)
  | some route =>
      match registry.registrations[request.action.rule.index]? with
      | none =>
          (failedInvocation request.action.key DispatchCode.missingRegistration, registry)
      | some registration =>
          match registry.packages[route.package]? with
          | none =>
              (failedInvocation request.action.key DispatchCode.missingPackage, registry)
          | some package =>
              match package.handlers[route.handler]? with
              | none =>
                  (failedInvocation request.action.key DispatchCode.missingHandler, registry)
              | some handler =>
                  if !registration.same handler.registration then
                    (failedInvocation request.action.key DispatchCode.registryMismatch, registry)
                  else if !RuleRequest.accepts handler.registration request then
                    (failedInvocation request.action.key DispatchCode.requestMismatch, registry)
                  else
                    let program : Program :=
                      { operations := request.program.operations
                        nodes := request.program.nodes }
                    let scopeAccepted :=
                      match registration.binding with
                      | .local | .global => true
                      | .scoped =>
                          registry.acceptsBinding program
                            { rule := request.action.key
                              anchor := request.action.node
                              watches := request.inputs.map (fun input => input.node)
                              writes := request.writes }
                    if !scopeAccepted then
                      (failedInvocation request.action.key
                          DispatchCode.requestMismatch, registry)
                    else
                      let (plan, cache) := handler.invoke package.cache request
                      let package :=
                        { package with
                          cache := cache
                          invocations := package.invocations + 1 }
                      (makeInvocation plan
                          (makeReplay handler.registration.key handler.replayFormats),
                        replacePackage registry route.package package)

/-- Explicitly evidence-discarding adapter for search experiments. A
proof-producing session must use `invokePlanned` and freeze its drafts before
submission. -/
def invokeDroppingDrafts (registry : Registry Fact) (request : RuleRequest Fact) :
    Outcome Fact × Registry Fact :=
  let (invocation, registry) := registry.invokePlanned request
  (invocation.plan.outcome, registry)

end Registry

end Hex.Interval.Experiment.Propagator
