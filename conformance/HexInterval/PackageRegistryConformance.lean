/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.PackageRegistry
import HexInterval.Experiment.PolicyDriver

/-!
Focused conformance for independently composable propagator packages.  The
fixtures deliberately combine unrelated private cache types, multiple rules
for one head, a package appended without central dispatch changes, malformed
requests, and an oversized resource refusal.
-/

namespace Hex.Interval.PackageRegistryConformance

open Experiment.Propagator

def real : DomainId := { index := 0 }
def other : DomainId := { index := 1 }

def sourceOp : OpKey := { name := "package-test.source" }
def sharedOp : OpKey := { name := "package-test.shared" }
def thirdOp : OpKey := { name := "package-test.third-party" }
def limitedOp : OpKey := { name := "package-test.resource" }
def externalOp : OpKey := { name := "package-test.frontend-owned" }

def tickKey : RuleKey := { name := "package-test.shared.tick" }
def observeKey : RuleKey := { name := "package-test.shared.observe" }
def thirdKey : RuleKey := { name := "package-test.third-party.forward" }
def limitedKey : RuleKey := { name := "package-test.resource.refuse" }
def externalKey : RuleKey := { name := "package-test.frontend-owned.observe" }

def sourceOperation : Operation := { key := sourceOp, inputs := [], output := real }
def sharedOperation : Operation := { key := sharedOp, inputs := [real], output := real }
def thirdOperation : Operation := { key := thirdOp, inputs := [real], output := real }
def limitedOperation : Operation := { key := limitedOp, inputs := [real], output := real }
def externalOperation : Operation := { key := externalOp, inputs := [real], output := real }

def tickRegistration : Registration :=
  { key := tickKey
    head := sharedOp
    kind := .improve
    watches := [.argument 0]
    writes := [] }

def observeRegistration : Registration :=
  { key := observeKey
    head := sharedOp
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def thirdRegistration : Registration :=
  { key := thirdKey
    head := thirdOp
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def limitedRegistration : Registration :=
  { key := limitedKey
    head := limitedOp
    kind := .improve
    watches := [.argument 0]
    writes := [] }

def externalRegistration : Registration :=
  { key := externalKey
    head := externalOp
    kind := .improve
    watches := [.argument 0]
    writes := [] }

def tickInvoke (cache : Nat) (_request : RuleRequest Nat) : Outcome Nat × Nat :=
  (.noChange { arithmeticWork := 1 }, cache + 1)

def observeInvoke (cache : Nat) (request : RuleRequest Nat) : Outcome Nat × Nat :=
  match request.writes with
  | [target] =>
      (.success [{ node := target, fact := 1, payload := { index := 1 } }]
        [] { arithmeticWork := 1 }, cache + 10)
  | _ => (.failed 32, cache)

/-- A separately appended package owns a `List Nat` cache.  Its mathematical
outcome is deliberately independent of that performance cache. -/
def thirdInvoke (cache : List Nat) (request : RuleRequest Nat) :
    Outcome Nat × List Nat :=
  match request.writes with
  | [target] =>
      (.success
        [{ node := target, fact := 2, payload := { index := 2 } }]
        [] { arithmeticWork := 1 }, request.action.node.index :: cache)
  | _ => (.failed 33, cache)

def limitedInvoke (_cache : Bool) (_request : RuleRequest Nat) : Outcome Nat × Bool :=
  (.resourceLimit 1000000, true)

def sharedPackage : Package Nat :=
  { Cache := Nat
    cache := 0
    operations := #[sourceOperation, sharedOperation]
    handlers :=
      #[Handler.bare tickRegistration tickInvoke,
        Handler.bare observeRegistration observeInvoke] }

def thirdPackage : Package Nat :=
  { Cache := List Nat
    cache := []
    operations := #[thirdOperation]
    requiredOperations := #[sourceOperation]
    handlers := #[Handler.bare thirdRegistration thirdInvoke] }

def limitedPackage : Package Nat :=
  { Cache := Bool
    cache := false
    operations := #[limitedOperation]
    handlers := #[Handler.bare limitedRegistration limitedInvoke]
    acceptsLimits := fun _ limits =>
      8 ≤ limits.maxObservationValue && 1000000 ≤ limits.maxDiagnosticValue }

/-- A package may attach a handler to a signature supplied only by the final
frontend program, but it must declare the exact dependency. -/
def externalPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    requiredOperations := #[externalOperation]
    handlers :=
      #[Handler.stateless externalRegistration (fun _ => .noChange {})] }

def duplicateRulePackage : Package Nat :=
  { Cache := Unit
    cache := ()
    requiredOperations := #[sharedOperation]
    handlers := #[Handler.stateless tickRegistration (fun _ => .inapplicable)] }

def undeclaredHeadPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    handlers := #[Handler.stateless tickRegistration (fun _ => .inapplicable)] }

def duplicateOperationPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sharedOperation]
    handlers := #[] }

def instruction (operation : Nat) (args : List NodeId := []) : Node :=
  { domain := real, op := { index := operation }, args }

def node (index : Nat) : NodeId := { index }

def program : Program :=
  { operations := #[sourceOperation, sharedOperation, thirdOperation, limitedOperation]
    nodes :=
      #[instruction 0,
        instruction 1 [node 0],
        instruction 2 [node 0],
        instruction 3 [node 0]] }

def mismatchedProgram : Program :=
  { operations :=
      #[sourceOperation,
        { sharedOperation with output := other },
        thirdOperation,
        limitedOperation]
    nodes := #[] }

def reorderedProgram : Program :=
  { operations := #[sourceOperation, thirdOperation, sharedOperation, limitedOperation]
    nodes :=
      #[instruction 0,
        instruction 2 [node 0],
        instruction 1 [node 0],
        instruction 3 [node 0]] }

def externalProgram : Program :=
  { operations := #[sourceOperation, externalOperation]
    nodes := #[instruction 0, instruction 1 [node 0]] }

def mismatchedExternalProgram : Program :=
  { operations :=
      #[sourceOperation, { externalOperation with inputs := [other] }]
    nodes := #[] }

def missingExternalProgram : Program :=
  { operations := #[sourceOperation], nodes := #[] }

def view : ProgramView :=
  { programVersion := 0
    operations := program.operations
    nodes := program.nodes
    generations := #[0, 0, 0, 0]
    depths := #[0, 1, 1, 1] }

def unaryRequest (rule application : Nat) (key : RuleKey) (anchor : NodeId)
    (kind : ActionKind) (writes : List NodeId) : RuleRequest Nat :=
  { action :=
      { serial := application
        programVersion := 0
        application := { index := application }
        rule := { index := rule }
        key
        node := anchor
        kind
        effort := 0
        inputs := [{ node := node 0, version := 0 }] }
    program := view
    inputs := [{ node := node 0, fact := 0, version := 0 }]
    writes }

def tickRequest : RuleRequest Nat :=
  unaryRequest 0 0 tickKey (node 1) .improve []

def observeRequest : RuleRequest Nat :=
  unaryRequest 1 1 observeKey (node 1) .forward [node 1]

def thirdRequest : RuleRequest Nat :=
  unaryRequest 2 2 thirdKey (node 2) .forward [node 2]

def wrongKeyRequest : RuleRequest Nat :=
  { tickRequest with action := { tickRequest.action with key := observeKey } }

def missingRouteRequest : RuleRequest Nat :=
  { tickRequest with action := { tickRequest.action with rule := { index := 99 } } }

def factDomain : FactDomain Nat where
  top _ := 0
  narrow _ current candidate :=
    if current < candidate then .improved candidate else .noChange

def limits : Limits :=
  { maxOperations := 8
    maxNodes := 8
    maxRules := 8
    maxArity := 2
    maxApplications := 8
    maxQueueEntries := 16
    maxActions := 16
    maxAcceptedFacts := 8
    maxRetainedSuggestions := 4
    maxEffort := 4
    maxObservationValue := 8
    maxDiagnosticValue := 1000000
    maxOutcomeCandidates := 2
    maxOutcomeSuggestions := 2
    maxProposalItems := 4
    maxInstances := 2
    maxGeneration := 2
    maxNodeDepth := 16
    maxEqualities := 2
    splitEndpointLimit :=
      { maxEndpointHeight := 16
        maxAlignmentShift := 8 } }

def registry? : Option (Registry Nat) :=
  match Registry.buildWithin limits #[sharedPackage, thirdPackage, limitedPackage] with
  | .ok registry => some registry
  | .error _ => none

def externalRegistry? : Option (Registry Nat) :=
  match Registry.buildWithin limits #[externalPackage] with
  | .ok registry => some registry
  | .error _ => none

def lowDiagnosticLimits : Limits :=
  { limits with maxDiagnosticValue := 999999 }

def shortRuleLimits : Limits :=
  { limits with maxRules := 3 }

def shortOperationLimits : Limits :=
  { limits with maxOperations := 3 }

def shortMetadataLimits : Limits :=
  { limits with maxOperations := 4, maxRules := 4 }

def nullaryLimits : Limits :=
  { limits with maxArity := 0 }

def run? : Option (RunResult Nat (Registry Nat)) :=
  match registry? with
  | none => none
  | some registry =>
      if !registry.acceptsProgram program || !registry.acceptsLimits program limits then none
      else
        match Engine.start factDomain program registry.registrations #[0, 0, 0, 0] limits with
        | .error _ => none
        | .ok state => some (drive Registry.invoke 12 state registry)

/-- Type-level conformance that the policy driver accepts the same
`Type 1` registry value as its private cache. -/
def policyDriverTypecheck {PolicyState : Type}
    (controller : Policy.Driver.Controller Nat PolicyState) (fuel : Nat)
    (state : Policy.State Nat) (registry : Registry Nat) (policyState : PolicyState) :
    Policy.Driver.Result Nat (Registry Nat) PolicyState :=
  Policy.Driver.drive controller Registry.invoke fuel state registry policyState

#guard program.check
#guard mismatchedProgram.check
#guard reorderedProgram.check
#guard externalProgram.check
#guard mismatchedExternalProgram.check
#guard missingExternalProgram.check

#guard
  match registry? with
  | some registry => !registry.acceptsLimits program lowDiagnosticLimits
  | none => false

-- Registry-owned dispatch failures have a diagnostic floor independent of
-- every package's callback-specific preflight.
#guard
  match Registry.buildWithin limits #[sharedPackage] with
  | .ok registry =>
      !registry.acceptsLimits program
          { limits with maxDiagnosticValue := DispatchCode.requestMismatch - 1 } &&
        registry.acceptsLimits program
          { limits with maxDiagnosticValue := DispatchCode.requestMismatch }
  | .error _ => false

#guard
  match Registry.buildWithin shortRuleLimits
      #[sharedPackage, thirdPackage, limitedPackage] with
  | .error (.resourceLimit .rules) => true
  | _ => false

#guard
  match Registry.buildWithin shortOperationLimits
      #[sharedPackage, thirdPackage, limitedPackage] with
  | .error (.resourceLimit .operations) => true
  | _ => false

#guard
  match Registry.buildWithin shortMetadataLimits
      #[sharedPackage, thirdPackage, limitedPackage] with
  | .error (.resourceLimit .registryEntries) => true
  | _ => false

#guard
  match Registry.buildWithin nullaryLimits
      #[sharedPackage, thirdPackage, limitedPackage] with
  | .error (.resourceLimit .arity) => true
  | _ => false

-- Package-major flattening preserves two distinct handlers for one head and
-- appends unrelated cache types without a central semantic dispatch edit.
#guard
  match registry? with
  | none => false
  | some registry =>
      registry.operations.size == 4 && registry.registrations.size == 4 &&
        registry.acceptsProgram program && registry.acceptsLimits program limits &&
        registry.acceptsProgram reorderedProgram &&
        !registry.acceptsProgram mismatchedProgram &&
        registry.routes ==
          #[{ package := 0, handler := 0 }, { package := 0, handler := 1 },
            { package := 1, handler := 0 }, { package := 2, handler := 0 }] &&
        (registry.operation? thirdOp).any fun operation => operation.key == thirdOp &&
        (reorderedProgram.operationEntry? thirdOp).any fun entry =>
          entry.1 == { index := 1 } && entry.2.key == thirdOp

#guard
  match externalRegistry? with
  | some registry =>
      registry.operations.isEmpty && registry.acceptsProgram externalProgram &&
        !registry.acceptsProgram mismatchedExternalProgram &&
        !registry.acceptsProgram missingExternalProgram
  | none => false

-- Exact duplicate semantic keys are rejected across package boundaries.
#guard
  match Registry.buildWithin limits #[sharedPackage, duplicateRulePackage] with
  | .error (.duplicateRule key) => key == tickKey
  | _ => false

#guard
  match Registry.buildWithin limits #[sharedPackage, duplicateOperationPackage] with
  | .error (.duplicateOperation key) => key == sharedOp
  | _ => false

#guard
  match Registry.buildWithin limits #[undeclaredHeadPackage] with
  | .error (.undeclaredHead rule head) => rule == tickKey && head == sharedOp
  | _ => false

-- Two handlers route through one package while an appended third-party
-- handler routes through another.  Their mathematical outcomes stay
-- cache-transparent; package invocation telemetry exposes isolation.
#guard
  match registry? with
  | none => false
  | some registry =>
      let (first, registry) := registry.invoke tickRequest
      let (second, registry) := registry.invoke observeRequest
      let (third, registry) := registry.invoke thirdRequest
      let (fourth, registry) := registry.invoke thirdRequest
      match first, second, third, fourth with
      | .noChange _, .success [observed] [] _,
          .success [initialThird] [] _, .success [cachedThird] [] _ =>
          observed.fact == 1 && initialThird.fact == 2 && cachedThird.fact == 2 &&
            registry.packages.map (fun package => package.invocations) == #[2, 2, 0]
      | _, _, _, _ => false

-- A valid route with the wrong stable key and an out-of-range RuleId both
-- fail before entering a callback.  Only the two later valid calls increment
-- package invocation telemetry.
#guard
  match registry? with
  | none => false
  | some registry =>
      let (wrong, registry) := registry.invoke wrongKeyRequest
      let (missing, registry) := registry.invoke missingRouteRequest
      let (tick, registry) := registry.invoke tickRequest
      let (observed, registry) := registry.invoke observeRequest
      match wrong, missing, tick, observed with
      | .failed wrongCode, .failed missingCode, .noChange _, .success [candidate] [] _ =>
          wrongCode == DispatchCode.requestMismatch &&
            missingCode == DispatchCode.missingRoute && candidate.fact == 1 &&
            registry.packages.map (fun package => package.invocations) == #[2, 0, 0]
      | _, _, _, _ => false

-- A corrupted static route is diagnosed before its unrelated handler can run.
#guard
  match registry? with
  | none => false
  | some registry =>
      let corrupted :=
        { registry with
          routes := registry.routes.set! 0 { package := 1, handler := 0 } }
      match (corrupted.invoke tickRequest).1 with
      | .failed code => code == DispatchCode.registryMismatch
      | _ => false

-- The million-unit number reports work refused before execution; it is not a
-- claimed cost observation, but it is checked by the separate diagnostic cap.
-- The engine accepts the boundary value, rejects one above it, and reaches a
-- genuine fixed point for the package accepted by start preflight.
#guard (Outcome.resourceLimit (Fact := Nat) 1000000).observationBounded 8 1000000
#guard !(Outcome.resourceLimit (Fact := Nat) 1000001).observationBounded 8 1000000

#guard
  match run? with
  | none => false
  | some result =>
      result.stop == .saturated && result.state.pending.isNone &&
        result.state.facts == #[0, 1, 2, 0] &&
        result.state.metrics.requests == 4 && result.state.metrics.replies == 4 &&
        result.state.metrics.improvements == 2 &&
        result.state.metrics.ruleNoChange == 1 &&
        result.state.metrics.ruleResourceLimits == 1 &&
        result.state.metrics.ruleFailures == 0

end Hex.Interval.PackageRegistryConformance
