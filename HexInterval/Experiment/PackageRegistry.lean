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
instead needs an explicit versioned dependency and wakeup protocol.  Immutable
proof-payload drafts travel beside the outcome; `PayloadSession` freezes them
in a separate per-run arena before their identifiers enter engine provenance.
-/

namespace Hex.Interval.Experiment.Propagator

/-- One package-produced result before its reply-local proof labels are frozen
into the run's immutable arena. -/
structure Plan (Fact : Type) where
  outcome : Outcome Fact
  drafts : List PayloadArena.Draft

/-- The callback shape shared by direct and session-owned drivers. -/
abbrev Invoke (Fact Cache : Type) :=
  Cache -> RuleRequest Fact -> Plan Fact × Cache

/-- Compatibility shape for a callback that produces no immutable evidence.
Its positive outcomes are deliberately rejected by the payload session if they
refer to any payload identifier. -/
abbrev BareInvoke (Fact Cache : Type) :=
  Cache -> RuleRequest Fact -> Outcome Fact × Cache

/-- One registration and the only callback allowed to interpret its key. -/
structure Handler (Fact Cache : Type) where
  registration : Registration
  invoke : Invoke Fact Cache

namespace Handler

/-- Lift a callback with no payload drafts into the planned protocol. -/
def bare (registration : Registration)
    (invoke : BareInvoke Fact Cache) : Handler Fact Cache :=
  { registration
    invoke := fun cache request =>
      let (outcome, cache) := invoke cache request
      ({ outcome, drafts := [] }, cache) }

/-- Lift a cache-independent callback into any package cache. -/
def readOnly (registration : Registration)
    (invoke : RuleRequest Fact -> Outcome Fact) : Handler Fact Cache :=
  bare registration fun cache request => (invoke request, cache)

/-- A cache-independent handler for a package whose cache is `Unit`. -/
def stateless (registration : Registration)
    (invoke : RuleRequest Fact -> Outcome Fact) : Handler Fact Unit :=
  readOnly registration invoke

/-- A cache-independent callback that returns complete reply-local evidence. -/
def readOnlyPlanned (registration : Registration)
    (invoke : RuleRequest Fact -> Plan Fact) : Handler Fact Cache :=
  { registration, invoke := fun cache request => (invoke request, cache) }

/-- A stateless callback that returns complete reply-local evidence. -/
def statelessPlanned (registration : Registration)
    (invoke : RuleRequest Fact -> Plan Fact) : Handler Fact Unit :=
  readOnlyPlanned registration invoke

end Handler

/-- An independently upgradeable collection of operations and handlers.

All handlers in one package share `Cache`; different packages in the same
registry may choose unrelated cache types.  `operations` contains signatures
introduced by this package, while `requiredOperations` records exact
signatures supplied elsewhere but interpreted by its matchers.  A handler may
target such an external operation; final head validation remains the engine's
responsibility once the complete program is available.  `acceptsLimits` is a
package-owned configuration preflight, not a soundness boundary: every reply
is still checked against the engine limits. -/
structure Package (Fact : Type) where
  Cache : Type
  cache : Cache
  operations : Array Operation := #[]
  requiredOperations : Array Operation := #[]
  handlers : Array (Handler Fact Cache)
  acceptsLimits : Program -> Limits -> Bool := fun _ _ => true
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

/-- Failure while flattening independently supplied packages. -/
inductive RegistryError where
  | duplicateOperation (key : OpKey)
  | duplicateRule (key : RuleKey)
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

def validateHandlerHeads (operations required : Array Operation) :
    List (Handler Fact Cache) -> Except RegistryError Unit
  | [] => pure ()
  | handler :: handlers =>
      if declaresOperation operations required handler.registration.head then
        validateHandlerHeads operations required handlers
      else
        throw (.undeclaredHead handler.registration.key handler.registration.head)

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
      validateHandlerHeads package.operations package.requiredOperations
        package.handlers.toList
      let operations <- addOperations package.operations.toList operations
      let (registrations, routes) <-
        addHandlers packageIndex 0 package.handlers.toList registrations routes
      flatten (packageIndex + 1) rest operations registrations routes

def preflight (limits : Limits) (packages : Array (Package Fact)) :
    Except RegistryError Unit := do
  if limits.maxOperations + limits.maxRules < packages.size then
    throw (.resourceLimit .registryEntries)
  let mut operationCount := 0
  let mut ruleCount := 0
  let mut metadataCount := 0
  for package in packages do
    operationCount := operationCount + package.operations.size
    ruleCount := ruleCount + package.handlers.size
    metadataCount := metadataCount + package.operations.size +
      package.requiredOperations.size + package.handlers.size
    if limits.maxOperations < operationCount then
      throw (.resourceLimit .operations)
    if limits.maxRules < ruleCount then
      throw (.resourceLimit .rules)
    if limits.maxOperations + limits.maxRules < metadataCount then
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
array allocation.  The aggregate metadata cap also bounds external signature
requirements and empty-package churn.  Assembly order is package-major and
then handler-major; exact operation and rule keys are unique in the snapshot. -/
def buildWithin (limits : Limits) (packages : Array (Package Fact)) :
    Except RegistryError (Registry Fact) :=
  match preflight limits packages with
  | .error error => .error error
  | .ok () =>
      match flatten 0 packages.toList #[] #[] #[] with
      | .error error => .error error
      | .ok (operations, registrations, routes) =>
          .ok { packages, operations, registrations, routes }

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

/-- Run every package-owned configuration preflight over the final program and
engine resource envelope. -/
def acceptsLimits (registry : Registry Fact) (program : Program)
    (limits : Limits) : Bool :=
  DispatchCode.requestMismatch ≤ limits.maxDiagnosticValue &&
    registry.packages.all fun package => package.acceptsLimits program limits

end Registry

namespace Registration

/-- Exact equality for immutable registration metadata. -/
def same (left right : Registration) : Bool :=
  left.key == right.key && left.head == right.head && left.kind == right.kind &&
    left.watches == right.watches && left.writes == right.writes &&
      left.watchesProgram == right.watchesProgram &&
      left.initialEffort == right.initialEffort

/-- Check that a routed handler sees the structural request projection
described by its immutable registration.  Engine-produced requests satisfy
this by construction; checking it here catches registry drift and malformed
direct test requests before a cache update.  Authentication of serials, fact
values, versions, and pending-state ownership remains the engine's job. -/
def accepts (registration : Registration) (request : RuleRequest Fact) : Bool :=
  if request.program.programVersion != request.action.programVersion then
    false
  else
    match request.program.node? request.action.node with
    | none => false
    | some anchor =>
        let inputNodes := request.inputs.map (fun input => input.node)
        let seen := request.inputs.map fun input =>
          { node := input.node, version := input.version : SeenVersion }
        registration.key == request.action.key &&
          registration.kind == request.action.kind &&
          request.program.operationKey? request.action.node == some registration.head &&
          resolveSlots? request.action.node anchor registration.watches == some inputNodes &&
          resolveSlots? request.action.node anchor registration.writes == some request.writes &&
          request.action.inputs == seen

end Registration

namespace Registry

/-- Route one engine-owned rule identifier to its package callback and retain
its reply-local proof drafts. Dispatch uses compact validated indices; it never
branches on the semantic operation or rule key. Only the selected package
cache is replaced. -/
def invokePlanned (registry : Registry Fact) (request : RuleRequest Fact) :
    Plan Fact × Registry Fact :=
  match registry.routes[request.action.rule.index]? with
  | none => ({ outcome := .failed DispatchCode.missingRoute, drafts := [] }, registry)
  | some route =>
      match registry.registrations[request.action.rule.index]? with
      | none =>
          ({ outcome := .failed DispatchCode.missingRegistration, drafts := [] }, registry)
      | some registration =>
          match registry.packages[route.package]? with
          | none => ({ outcome := .failed DispatchCode.missingPackage, drafts := [] }, registry)
          | some package =>
              match package.handlers[route.handler]? with
              | none =>
                  ({ outcome := .failed DispatchCode.missingHandler, drafts := [] }, registry)
              | some handler =>
                  if !registration.same handler.registration then
                    ({ outcome := .failed DispatchCode.registryMismatch, drafts := [] }, registry)
                  else if !handler.registration.accepts request then
                    ({ outcome := .failed DispatchCode.requestMismatch, drafts := [] }, registry)
                  else
                    let (plan, cache) := handler.invoke package.cache request
                    let package :=
                      { package with
                        cache := cache
                        invocations := package.invocations + 1 }
                    (plan,
                      { registry with
                        packages := registry.packages.set! route.package package })

/-- Compatibility adapter for search experiments that do not yet retain proof
payloads. Proof-producing runs use `invokePlanned` through `PayloadSession`. -/
def invoke (registry : Registry Fact) (request : RuleRequest Fact) :
    Outcome Fact × Registry Fact :=
  let (plan, registry) := registry.invokePlanned request
  (plan.outcome, registry)

end Registry

end Hex.Interval.Experiment.Propagator
