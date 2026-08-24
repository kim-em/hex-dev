/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Controller
import HexIntervalMathlib.DriverConformance

/-!
# Autonomous controller conformance

The generator table drives the existing nontrivial root-update, split,
child-update, target, and sibling-refutation canary without caller-selected
actions.  The resulting sealed bundle replays through the separately aligned
proof registry to the same ordinary theorem.
-/

namespace Hex.IntervalMathlib.ControllerConformance

open Hex.Interval
open Hex.Interval.Proof
open Hex.IntervalMathlib.DriverConformance

/-- error: Unknown constant `Hex.Interval.Controller.Registry.mk` -/
#guard_msgs in
#check Controller.Registry.mk

/-- error: Unknown constant `Hex.Interval.Controller.State.mk` -/
#guard_msgs in
#check Controller.State.mk

/-- error: Unknown constant `Hex.Interval.Controller.Draft.age` -/
#guard_msgs in
#check Controller.Draft.age

/-- error: Unknown constant `Hex.Interval.Controller.runWithin.loop` -/
#guard_msgs in
#check Controller.runWithin.loop

private def version? (branch : State.Branch Fact Nat) (node : NodeId) : Option Nat :=
  branch.versions[node.index]?

private def scopedBinding (rule : RuleKey) (anchor : NodeId)
    (inputs writes : List NodeId) : Option ScopeBinding :=
  some { rule, anchor, watches := inputs, writes }

def forwardApplication : Controller.Application Fact Nat Nat :=
  { binding := fun selectedScope _ =>
      if selectedScope == scope then
        scopedBinding forwardRule n2 [n1] [n2]
      else if selectedScope == leftScope then
        scopedBinding forwardRule n3 [n0] [n3]
      else none
    offer := fun selectedScope branch =>
      if selectedScope == scope && version? branch n2 == some 0 then
        some
          { key := 10
            offerClass := .invoke
            node := n2
            effort := 0
            inputs := [n1]
            writes := [n2] }
      else if selectedScope == leftScope && version? branch n3 == some 0 then
        some
          { key := 11
            offerClass := .invoke
            node := n3
            effort := 0
            inputs := [n0]
            writes := [n3] }
      else none }

def targetApplication : Controller.Application Fact Nat Nat :=
  { binding := fun selectedScope _ =>
      if selectedScope == leftScope then
        scopedBinding forwardRule n3 [n3] [n3]
      else none
    offer := fun selectedScope branch =>
      if selectedScope == leftScope && version? branch n3 == some 1 then
        some
          { key := 12
            offerClass := .invoke
            node := n3
            effort := 0
            inputs := [n3]
            writes := [n3] }
      else none }

/-- A second root offer for the same runtime rule. Its table position and
semantic key make the simultaneous snapshot order observable. -/
def secondForwardApplication : Controller.Application Fact Nat Nat :=
  { binding := forwardApplication.binding
    offer := fun selectedScope branch =>
      if selectedScope == scope && version? branch n2 == some 0 then
        some
          { key := 13
            offerClass := .invoke
            node := n2
            effort := 0
            inputs := [n1]
            writes := [n2] }
      else none }

def splitApplication : Controller.Application Fact Nat Nat :=
  { binding := fun selectedScope _ =>
      if selectedScope == scope then
        scopedBinding splitRule n0 [n1, n0] []
      else none
    offer := fun selectedScope branch =>
      if selectedScope == scope && version? branch n2 == some 1 then
        some
          { key := 20
            offerClass := .split
            node := n0
            effort := 0
            inputs := [n1, n0] }
      else none }

def refuteApplication : Controller.Application Fact Nat Nat :=
  { binding := fun selectedScope _ =>
      if selectedScope == rightScope then scopedBinding refuteRule n0 [n0] [] else none
    offer := fun selectedScope _ =>
      if selectedScope == rightScope then
        some
          { key := 30
            offerClass := .invoke
            node := n0
            effort := 0
            inputs := [n0] }
      else none }

private def updateC (request : Search.Request Fact Controller.OfferId Nat)
    (node : NodeId) (previous : SeenVersion) (fact : Fact) (version cause : Nat) :
    State.Update Fact Nat :=
  { programVersion := request.programVersion, node, previous, fact, version, cause }

private def eventC (request : Search.Request Fact Controller.OfferId Nat)
    (item : State.Update Fact Nat) : Proof.Event Fact :=
  .fact
    { scope := request.scope, programVersion := request.programVersion,
      action := request.action, node := item.node, previous := item.previous,
      version := item.version, proposed := item.fact, installed := item.fact,
      assumptions := request.action.inputs, schema := factKey, body := [11] }

private def outcomeC (request : Search.Request Fact Controller.OfferId Nat)
    (updates : Array (State.Update Fact Nat)) :
    Search.Outcome Fact Nat Controller.OfferId Nat :=
  { scope := request.scope, serial := request.serial,
    programVersion := request.programVersion, offer := request.offer,
    action := request.action, updates }

def forwardRuntime : Driver.Package Fact Nat Controller.OfferId Nat (List Nat) :=
  { rule := forwardRule
    invoke := fun request =>
      if request.scope == scope then
        let item := updateC request n2 (seen n2 0) .yes 1 1
        .continue { outcome := outcomeC request #[item], events := [eventC request item] }
      else if request.scope == leftScope && request.action.inputs == [seen n0 0] then
        let item := updateC request n3 (seen n3 0) .yes 1 2
        .continue { outcome := outcomeC request #[item], events := [eventC request item] }
      else
        .target { outcome := outcomeC request #[], events := [] }
          { scope := request.scope, programVersion := request.programVersion,
            seen := seen n3 1 } }

def splitRuntime : Driver.Package Fact Nat Controller.OfferId Nat (List Nat) :=
  { rule := splitRule
    invoke := fun request =>
      .split
        { echo := { outcome := outcomeC request #[], events := [] }
          runtime :=
            { scope := request.scope, programVersion := request.programVersion,
              action := request.action, parent := seen n0 0, plan := [22],
              schema := splitKey, body := [22] }
          left := { node := n0, previous := seen n0 0, fact := .yes }
          right := { node := n0, previous := seen n0 0, fact := .empty } } }

def refuteRuntime : Driver.Package Fact Nat Controller.OfferId Nat (List Nat) :=
  { rule := refuteRule
    invoke := fun request =>
      .refute { outcome := outcomeC request #[], events := [] }
        { scope := request.scope, programVersion := request.programVersion,
          seen := seen n0 0, schema := refuteKey, body := [33] } }

def packages : Array (Controller.Package Fact Nat Nat (List Nat)) :=
  #[{ runtime := forwardRuntime, applications := #[forwardApplication, targetApplication] },
    { runtime := splitRuntime, applications := #[splitApplication] },
    { runtime := refuteRuntime, applications := #[refuteApplication] }]

def controllerLimits : Controller.Limits :=
  { maxChoices := 5, policyState := { bytes := 4, pairs := 4, work := 4 }, driver := limits }

def keyCost (_ : Nat) : Policy.Cost := { bytes := 1, work := 1 }

def unitCost (_ : Unit) : Policy.Cost := { bytes := 1, work := 1 }

def firstPolicy : Policy.Interface Fact Unit Controller.OfferId Nat :=
  { choose := fun _ view =>
      match view.offers[0]? with
      | some offer => .select offer ()
      | none => .stop () }

def controllerKey : Controller.Key := { name := "controller-canary", version := 1 }

def controllerRegistry? := do
  let proof ← registry?
  (Controller.Registry.buildWithin stateLimits controllerKey program proof packages).toOption

def twoOfferPackages : Array (Controller.Package Fact Nat Nat (List Nat)) :=
  #[{ runtime := forwardRuntime,
      applications := #[forwardApplication, secondForwardApplication] },
    { runtime := splitRuntime, applications := #[splitApplication] },
    { runtime := refuteRuntime, applications := #[refuteApplication] }]

def twoOfferRegistry? := do
  let proof ← registry?
  (Controller.Registry.buildWithin stateLimits controllerKey program proof twoOfferPackages).toOption

def twoOfferEnvelope : Search.Envelope :=
  { envelope with policy := { policyLimits with maxOffers := 2 } }

def run := do
  let some registry := controllerRegistry? | throw 1
  let branch ← (State.Branch.startWithin stateLimits program input.facts).mapError fun _ => 2
  let bundle ← (Driver.Bundle.startWithin limits resultMeasure recipeMeasure scope branch)
    |>.mapError fun _ => 3
  let measure := Controller.policyMeasure keyCost
  let state ← (Controller.State.startWithin envelope measure registry bundle).mapError fun _ => 4
  let result ← (Controller.runWithin controllerLimits envelope keyCost unitCost resultMeasure
    recipeMeasure .depthFirst registry firstPolicy () state).mapError fun _ => 5
  let .complete bundle _ := result | throw 6
  pure bundle

def replayRun := do
  let some registry := controllerRegistry? | throw Proof.Error.invalidInput
  let bundle ← run |>.mapError fun _ => Proof.Error.wrongTree
  Proof.replayTree resultLimits resultMeasure proofLimits treeLimits registry.proof
    factDomain laws input bundle.tree bundle.recipe

#guard match run with | .ok _ => true | .error _ => false
#guard match replayRun with | .ok _ => true | .error _ => false

def wrongOwnerPackages : Array (Controller.Package Fact Nat Nat (List Nat)) :=
  #[{ runtime := { forwardRuntime with rule := splitRule },
      applications := #[forwardApplication, targetApplication] },
    { runtime := splitRuntime, applications := #[splitApplication] },
    { runtime := refuteRuntime, applications := #[refuteApplication] }]

def wrongOwnerRejected : Bool :=
  match registry? with
  | none => false
  | some proof =>
      match Controller.Registry.buildWithin stateLimits controllerKey program proof wrongOwnerPackages with
      | .error _ => true
      | .ok _ => false

def generationRejected : Bool :=
  let tooNew : Controller.Application Fact Nat Nat :=
    { forwardApplication with generation := stateLimits.maxGeneration + 1 }
  match packages[0]?, registry? with
  | some first, some proof =>
      let changed := packages.set! 0 { first with applications := #[tooNew] }
      match Controller.Registry.buildWithin stateLimits controllerKey program proof changed with
      | .error (.resource (.state .generation)) => true
      | _ => false
  | _, _ => false

def choiceOneOver : Bool :=
  match controllerRegistry? with
  | none => false
  | some registry =>
      match State.Branch.startWithin stateLimits program input.facts with
      | .error _ => false
      | .ok branch =>
          match Driver.Bundle.startWithin limits resultMeasure recipeMeasure scope branch with
          | .error _ => false
          | .ok bundle =>
              let measure := Controller.policyMeasure keyCost
              match Controller.State.startWithin envelope measure registry bundle with
              | .error _ => false
              | .ok state =>
                  match Controller.runWithin { controllerLimits with maxChoices := 0 } envelope
                      keyCost unitCost resultMeasure recipeMeasure .depthFirst registry firstPolicy ()
                      state with
                  | .error (.resource .choices) => true
                  | _ => false

/-- The live successful canary needs all five selections; four is the exact
one-under cap rather than a degenerate zero-step refusal. -/
def choiceFiveNeedsCap : Bool :=
  match controllerRegistry? with
  | none => false
  | some registry =>
      match State.Branch.startWithin stateLimits program input.facts with
      | .error _ => false
      | .ok branch =>
          match Driver.Bundle.startWithin limits resultMeasure recipeMeasure scope branch with
          | .error _ => false
          | .ok bundle =>
              match Controller.State.startWithin envelope (Controller.policyMeasure keyCost)
                  registry bundle with
              | .error _ => false
              | .ok state =>
                  match Controller.runWithin { controllerLimits with maxChoices := 4 } envelope
                      keyCost unitCost resultMeasure recipeMeasure .depthFirst registry firstPolicy
                      () state with
                  | .error (.resource .choices) => true
                  | _ => false

#guard wrongOwnerRejected
#guard generationRejected
#guard choiceOneOver
#guard choiceFiveNeedsCap

private def withForward
    (applications : Array (Controller.Application Fact Nat Nat)) :
    Array (Controller.Package Fact Nat Nat (List Nat)) :=
  match packages[0]? with
  | none => #[]
  | some first => packages.set! 0 { first with applications }

def providerOneOver : Bool :=
  let tooMany := withForward #[forwardApplication, targetApplication, forwardApplication,
    targetApplication, forwardApplication]
  match registry? with
  | none => false
  | some proof =>
      match Controller.Registry.buildWithin stateLimits controllerKey program proof tooMany with
      | .error (.resource .applications) => true
      | _ => false

private def stateStartWith
    (candidateEnvelope : Search.Envelope)
    (registry : Controller.Registry Fact semantics Nat Nat (List Nat)) := do
  let branch ← State.Branch.startWithin stateLimits program input.facts
    |>.mapError fun _ => Controller.Error.mismatch
  let bundle ← Driver.Bundle.startWithin limits resultMeasure recipeMeasure scope branch
    |>.mapError Controller.Error.driver
  Controller.State.startWithin candidateEnvelope (Controller.policyMeasure keyCost)
    registry bundle

def listCost (values : List Nat) : Policy.Cost :=
  { bytes := values.length, pairs := values.length, work := values.length }

def hugeStatePolicy : Policy.Interface Fact (List Nat) Controller.OfferId Nat :=
  { choose := fun _ _ => .stop (List.replicate 5 0) }

def hugeInitialPolicyRejected : Bool :=
  match controllerRegistry? with
  | none => false
  | some registry =>
      match stateStartWith envelope registry with
      | .error _ => false
      | .ok state =>
          match Controller.runWithin controllerLimits envelope keyCost listCost resultMeasure
              recipeMeasure .depthFirst registry hugeStatePolicy (List.replicate 5 0) state with
          | .error (.resource .policyState) => true
          | _ => false

def hugeNextPolicyRejected : Bool :=
  match controllerRegistry? with
  | none => false
  | some registry =>
      match stateStartWith envelope registry with
      | .error _ => false
      | .ok state =>
          match Controller.runWithin controllerLimits envelope keyCost listCost resultMeasure
              recipeMeasure .depthFirst registry hugeStatePolicy [] state with
          | .error (.resource .policyState) => true
          | _ => false

#guard hugeInitialPolicyRejected
#guard hugeNextPolicyRejected

def offerOneOver : Bool :=
  match controllerRegistry? with
  | none => false
  | some registry =>
      let tight : Search.Envelope :=
        { envelope with policy := { policyLimits with maxOffers := 0 } }
      match stateStartWith tight registry with
      | .error (.search (.policy .offerLimit)) => true
      | _ => false

def hugeDraftApplication : Controller.Application Fact Nat Nat :=
  { forwardApplication with
    offer := fun selectedScope _ =>
      if selectedScope == scope then
        some
          { key := 40
            offerClass := .invoke
            node := n2
            effort := 0
            inputs := List.replicate 3 n1
            writes := [n2] }
      else none }

def hugeDraftRejected : Bool :=
  let changed := withForward #[hugeDraftApplication, targetApplication]
  match registry? with
  | none => false
  | some proof =>
      match Controller.Registry.buildWithin stateLimits controllerKey program proof changed with
      | .error _ => false
      | .ok registry =>
          match stateStartWith envelope registry with
          | .error (.resource (.state .scopes)) => true
          | _ => false

def hugeBindingApplication : Controller.Application Fact Nat Nat :=
  { forwardApplication with
    binding := fun selectedScope _ =>
      if selectedScope == scope then
        scopedBinding forwardRule n2 (List.replicate 3 n1) [n2]
      else none }

def hugeBindingRejected : Bool :=
  let changed := withForward #[hugeBindingApplication, targetApplication]
  match registry? with
  | none => false
  | some proof =>
      match Controller.Registry.buildWithin stateLimits controllerKey program proof changed with
      | .error _ => false
      | .ok registry =>
          match stateStartWith envelope registry with
          | .error (.resource (.state .scopes)) => true
          | _ => false

def hugeEffortApplication : Controller.Application Fact Nat Nat :=
  { forwardApplication with
    offer := fun selectedScope _ =>
      if selectedScope == scope then
        some
          { key := 42
            offerClass := .invoke
            node := n2
            effort := stateLimits.maxEffort + 1
            inputs := [n1]
            writes := [n2] }
      else none }

def effortOneOver : Bool :=
  let changed := withForward #[hugeEffortApplication, targetApplication]
  match registry? with
  | none => false
  | some proof =>
      match Controller.Registry.buildWithin stateLimits controllerKey program proof changed with
      | .error _ => false
      | .ok registry =>
          match stateStartWith envelope registry with
          | .error (.resource (.state .effort)) => true
          | _ => false

def structuralApplication : Controller.Application Fact Nat Nat :=
  { forwardApplication with
    offer := fun selectedScope _ =>
      if selectedScope == scope then
        some
          { key := 43
            offerClass := .invoke
            node := n2
            effort := 0
            inputs := [n1]
            writes := [n2]
            structuralInputs := [.node n1] }
      else none }

def structuralBatchRejected : Bool :=
  let changed := withForward #[structuralApplication, targetApplication]
  match registry? with
  | none => false
  | some proof =>
      match Controller.Registry.buildWithin stateLimits controllerKey program proof changed with
      | .error _ => false
      | .ok registry =>
          match stateStartWith envelope registry with
          | .error (.resource (.state .matcherVisits)) => true
          | _ => false

def networkRegistration : Registration :=
  { key := forwardRule
    head := sourceKey
    kind := .instantiate
    watches := []
    writes := []
    binding := .global
    matchWatch := .network
    watchesProgram := true }

def networkProof? : Option (Proof.Registry semantics (List Nat)) :=
  let changed : Proof.Package semantics (List Nat) :=
    { package with registrations := registrations.set! 0 networkRegistration }
  (Proof.Registry.buildWithin proofLimits program #[changed]).toOption

private def networkApplication
    (structuralInputs : List StructuralKey) : Controller.Application Fact Nat Nat :=
  { offer := fun selectedScope _ =>
      if selectedScope == scope then
        some
          { key := 45
            offerClass := .instantiate
            node := n2
            effort := 0
            inputs := []
            writes := []
            structuralInputs }
      else none }

private def networkRegistry?
    (structuralInputs : List StructuralKey) := do
  let proof ← networkProof?
  let changed := withForward #[networkApplication structuralInputs]
  (Controller.Registry.buildWithin stateLimits controllerKey program proof changed).toOption

def networkEnvelope : Search.Envelope :=
  { envelope with state := { stateLimits with matcherBatchSize := 1 } }

def emptyNetworkRejected : Bool :=
  match networkRegistry? [] with
  | none => false
  | some registry =>
      match stateStartWith networkEnvelope registry with
      | .error (.invalidApplication ⟨0⟩) => true
      | _ => false

def networkStructuralAccepted : Bool :=
  match networkRegistry? [.node n1] with
  | none => false
  | some registry =>
      match stateStartWith networkEnvelope registry with
      | .error _ => false
      | .ok state =>
          match state.session.offers[0]? with
          | none => false
          | some offer =>
              offer.action.kind == .instantiate && offer.action.inputs.isEmpty &&
                offer.action.writes.isEmpty && offer.action.matcherEpoch == some 0 &&
                offer.action.structuralInputs ==
                  [{ key := .node n1, generation := 0 }]

private def malformedDraftApplication
    (inputs writes : List NodeId) (structuralInputs : List StructuralKey)
    (node : NodeId := n2) : Controller.Application Fact Nat Nat :=
  { forwardApplication with
    offer := fun selectedScope _ =>
      if selectedScope == scope then
        some
          { key := 44
            offerClass := .invoke
            node
            effort := 0
            inputs
            writes
            structuralInputs }
      else none }

private def malformedDraftRejected
    (application : Controller.Application Fact Nat Nat)
    (candidateEnvelope : Search.Envelope := envelope) : Bool :=
  let changed := withForward #[application, targetApplication]
  match registry? with
  | none => false
  | some proof =>
      match Controller.Registry.buildWithin stateLimits controllerKey program proof changed with
      | .error _ => false
      | .ok registry =>
          match stateStartWith candidateEnvelope registry with
          | .error (.invalidApplication ⟨0⟩) => true
          | _ => false

-- Scoped bindings remain sets of authority-bearing nodes, so a duplicate
-- draft cannot be correlated with the separately validated binding table.
def scopedDuplicateInputsRejected : Bool :=
  malformedDraftRejected (malformedDraftApplication [n1, n1] [n2] [])

def duplicateWritesRejected : Bool :=
  malformedDraftRejected (malformedDraftApplication [n1] [n2, n2] [])

def duplicateStructuralRejected : Bool :=
  let structuralEnvelope : Search.Envelope :=
    { envelope with state := { stateLimits with matcherBatchSize := 2 } }
  malformedDraftRejected
    (malformedDraftApplication [n1] [n2] [.node n1, .node n1]) structuralEnvelope

/-! ## Local repeated-read occurrences -/

def repeatOperationKey : OpKey := { name := "controller-repeat" }
def repeatControllerRule : RuleKey := { name := "controller-repeat-forward", schema := 1 }

def repeatOperation : Operation :=
  { key := repeatOperationKey, inputs := [domain, domain], output := domain }

def repeatProgram : Program :=
  { operations := #[operation, repeatOperation]
    nodes :=
      #[sourceNode,
        { domain, op := { index := 1 }, args := [n0, n0] }] }

def repeatRegistration : Registration :=
  { key := repeatControllerRule, head := repeatOperationKey, kind := .forward,
    watches := [.argument 0, .argument 1], writes := [] }

def repeatProofPackage : Proof.Package semantics (List Nat) :=
  { registrations := #[repeatRegistration] }

def repeatStateLimits : State.Limits :=
  { stateLimits with
    maxOperations := 2
    maxNodes := 2
    maxRules := 1
    maxRegistryEntries := 1
    maxApplications := 1
    maxNodeDepth := 1 }

def repeatProofRegistry? : Option (Proof.Registry semantics (List Nat)) :=
  (Proof.Registry.buildWithin proofLimits repeatProgram #[repeatProofPackage]).toOption

def repeatApplication : Controller.Application Fact Nat Nat :=
  { offer := fun selectedScope branch =>
      if selectedScope == scope && version? branch n1 == some 0 then
        some
          { key := 45
            offerClass := .invoke
            node := n1
            effort := 0
            inputs := [n0, n0] }
      else none }

def repeatRuntime : Driver.Package Fact Nat Controller.OfferId Nat (List Nat) :=
  { rule := repeatControllerRule
    invoke := fun request =>
      if request.action.inputs == [seen n0 0, seen n0 0] then .stop 7 else .stop 8 }

def repeatPackages : Array (Controller.Package Fact Nat Nat (List Nat)) :=
  #[{ runtime := repeatRuntime, applications := #[repeatApplication] }]

def repeatControllerRegistry? := do
  let proof ← repeatProofRegistry?
  (Controller.Registry.buildWithin repeatStateLimits controllerKey repeatProgram proof
    repeatPackages).toOption

def repeatRuntimeLimits : Runtime.Limits :=
  { runtimeLimits with executable :=
      { runtimeLimits.executable with state := repeatStateLimits } }

def repeatResultLimits : Search.Result.Limits :=
  { resultLimits with runtime := repeatRuntimeLimits }

def repeatDriverLimits : Driver.Limits :=
  { limits with result := repeatResultLimits }

def repeatControllerLimits : Controller.Limits :=
  { controllerLimits with maxChoices := 1, driver := repeatDriverLimits }

def repeatEnvelope : Search.Envelope :=
  { envelope with state := repeatStateLimits }

def repeatControllerAccepted : Bool :=
  match repeatControllerRegistry? with
  | none => false
  | some registry =>
      match State.Branch.startWithin repeatStateLimits repeatProgram
          #[Fact.yes, Fact.all] with
      | .error _ => false
      | .ok branch =>
          match Driver.Bundle.startWithin repeatDriverLimits resultMeasure
              recipeMeasure scope branch with
          | .error _ => false
          | .ok bundle =>
              match Controller.State.startWithin repeatEnvelope
                  (Controller.policyMeasure keyCost) registry bundle with
              | .error _ => false
              | .ok state =>
                  state.session.offers[0]?.any (fun offer =>
                    offer.action.inputs == [seen n0 0, seen n0 0]) &&
                    match Controller.runWithin repeatControllerLimits repeatEnvelope keyCost
                        unitCost resultMeasure recipeMeasure .depthFirst registry firstPolicy () state with
                    | .ok (.stopped (.callbackFailure 7) stopped ()) =>
                        stopped.choices == 1
                    | _ => false

def missingNodeRejected : Bool :=
  malformedDraftRejected
    (malformedDraftApplication [n1] [n2] [] { index := program.nodes.size })

def wrongClassApplication : Controller.Application Fact Nat Nat :=
  { forwardApplication with
    offer := fun selectedScope branch =>
      if selectedScope == scope && version? branch n2 == some 0 then
        some
          { key := 41
            offerClass := .split
            node := n2
            effort := 0
            inputs := [n1]
            writes := [n2] }
      else none }

def wrongClassRejected : Bool :=
  let changed := withForward #[wrongClassApplication, targetApplication]
  match registry? with
  | none => false
  | some proof =>
      match Controller.Registry.buildWithin stateLimits controllerKey program proof changed with
      | .error _ => false
      | .ok registry =>
          match stateStartWith envelope registry with
          | .error (.invalidApplication ⟨0⟩) => true
          | _ => false

def transplantRejected : Bool :=
  match registry?, controllerRegistry? with
  | some proof, some registry =>
      let otherKey : Controller.Key := { name := "controller-canary", version := 2 }
      match Controller.Registry.buildWithin stateLimits otherKey program proof packages with
      | .error _ => false
      | .ok other =>
          match stateStartWith envelope registry with
          | .error _ => false
          | .ok state =>
              match Controller.runWithin controllerLimits envelope keyCost unitCost resultMeasure
                  recipeMeasure .depthFirst other firstPolicy () state with
              | .error .mismatch => true
              | _ => false
  | _, _ => false

def matcherEpochRejected : Bool :=
  match registry? with
  | none => false
  | some proof =>
      match Controller.Registry.buildWithin stateLimits controllerKey program proof packages
          #[] (stateLimits.maxGeneration + 1) with
      | .error (.resource (.state .generation)) => true
      | _ => false

def oneThenStop : Policy.Interface Fact Nat Controller.OfferId Nat :=
  { choose := fun count view =>
      if count == 0 then
        match view.offers[0]? with
        | some offer => .select offer 1
        | none => .stop count
      else .stop count }

def dismissThenStop : Policy.Interface Fact Bool Controller.OfferId Nat :=
  { choose := fun dismissed view =>
      if dismissed then .stop true else
        match view.offers[0]? with
        | some offer => .dismiss offer true
        | none => .stop false }

def boolCost (_ : Bool) : Policy.Cost := { bytes := 1, work := 1 }

def dismissFirstSelectSecond : Policy.Interface Fact Nat Controller.OfferId Nat :=
  { choose := fun stage view =>
      match stage with
      | 0 => match view.offers[0]? with
        | some offer => .dismiss offer 1
        | none => .stop 0
      | 1 => match view.offers[0]? with
        | some offer => .select offer 2
        | none => .stop 1
      | _ => .stop stage }

private def retainedFactApplication
    (bundle : Driver.Bundle Fact Nat (List Nat)) (application : Nat) : Bool :=
  match bundle.recipe.events[0]? with
  | none => false
  | some events => events.any fun
      | .fact step => step.action.application.index == application
      | _ => false

def twoOffersOrdered : Bool :=
  match twoOfferRegistry? with
  | none => false
  | some registry =>
      match stateStartWith twoOfferEnvelope registry with
      | .error _ => false
      | .ok state =>
          match state.session.offers[0]?, state.session.offers[1]? with
          | some first, some second =>
              state.session.offers.size == 2 && first.view.id.index == 0 &&
                first.view.key == 10 && second.view.id.index == 1 && second.view.key == 13
          | _, _ => false

/-- Dismissing the first non-split offer remains sticky after accepting the
second simultaneous offer and regenerating the current root snapshot. -/
def dismissThenSelectSticky : Bool :=
  match twoOfferRegistry? with
  | none => false
  | some registry =>
      match stateStartWith twoOfferEnvelope registry with
      | .error _ => false
      | .ok state =>
          match Controller.runWithin controllerLimits twoOfferEnvelope keyCost
              (fun _ => { bytes := 1 }) resultMeasure recipeMeasure .depthFirst registry
              dismissFirstSelectSecond 0 state with
          | .ok (.stopped (.policyStop 1) stopped 2) =>
              stopped.choices == 2 && stopped.dismissedIncomplete &&
                stopped.session.incomplete && stopped.session.serial == 1 &&
                version? stopped.session.branch n2 == some 1 &&
                retainedFactApplication stopped.bundle 1 &&
                (match stopped.session.offers[0]? with
                | some offer => offer.view.id.index == 2 && offer.view.offerClass == .split
                | none => false)
          | _ => false

/-- Starting explicitly from the same stopped bundle creates a new run handle:
the retained pending head remains, while controller and search chronology reset
without inheriting the old handle's incompleteness or any closure claim. -/
def restartResetsHandle : Bool :=
  match twoOfferRegistry? with
  | none => false
  | some registry =>
      match stateStartWith twoOfferEnvelope registry with
      | .error _ => false
      | .ok state =>
          match Controller.runWithin controllerLimits twoOfferEnvelope keyCost
              (fun _ => { bytes := 1 }) resultMeasure recipeMeasure .depthFirst registry
              dismissFirstSelectSecond 0 state with
          | .ok (.stopped (.policyStop 1) sticky 2) =>
              match Controller.State.startWithin twoOfferEnvelope
                  (Controller.policyMeasure keyCost) registry sticky.bundle with
              | .error _ => false
              | .ok restarted =>
                  sticky.choices == 2 && sticky.dismissedIncomplete &&
                    sticky.session.serial == 1 && sticky.session.steps == 1 &&
                    restarted.session.scope == sticky.session.scope &&
                    restarted.choices == 0 && !restarted.dismissedIncomplete &&
                    restarted.session.serial == 0 && restarted.session.steps == 0 &&
                    restarted.session.trace.events.isEmpty &&
                    restarted.session.trace.bytes == 0 && restarted.session.trace.work == 0 &&
                    !restarted.session.trace.truncated && !restarted.session.incomplete &&
                    (Search.Result.current? restarted.bundle.tree).isSome &&
                    restarted.session.offers.size == 1
          | _ => false

def stickyClearsAtSplit : Bool :=
  match twoOfferRegistry? with
  | none => false
  | some registry =>
      match stateStartWith twoOfferEnvelope registry with
      | .error _ => false
      | .ok state =>
          match Controller.runWithin controllerLimits twoOfferEnvelope keyCost
              (fun _ => { bytes := 1 }) resultMeasure recipeMeasure .depthFirst registry
              dismissFirstSelectSecond 0 state with
          | .ok (.stopped (.policyStop 1) sticky 2) =>
              match Controller.runWithin controllerLimits twoOfferEnvelope keyCost
                  (fun _ => { bytes := 1 }) resultMeasure recipeMeasure .depthFirst registry
                  oneThenStop 0 sticky with
              | .ok (.stopped (.policyStop 1) child 1) =>
                  child.choices == 3 && child.session.scope == leftScope &&
                    !child.dismissedIncomplete && !child.session.incomplete
              | _ => false
          | _ => false

def dismissedInvokeIncomplete : Bool :=
  match controllerRegistry? with
  | none => false
  | some registry =>
      match stateStartWith envelope registry with
      | .error _ => false
      | .ok state =>
          match Controller.runWithin controllerLimits envelope keyCost boolCost resultMeasure
              recipeMeasure .depthFirst registry dismissThenStop false state with
          | .ok (.stopped (.policyStop 0) state true) =>
              state.choices == 1 && state.session.incomplete && state.session.offers.isEmpty
          | _ => false

def dismissedSplitComplete : Bool :=
  match controllerRegistry? with
  | none => false
  | some registry =>
      match stateStartWith envelope registry with
      | .error _ => false
      | .ok state =>
          match Controller.runWithin controllerLimits envelope keyCost (fun _ => { bytes := 1 })
              resultMeasure recipeMeasure .depthFirst registry oneThenStop 0 state with
          | .ok (.stopped (.policyStop 1) splitState 1) =>
              match Controller.runWithin controllerLimits envelope keyCost boolCost resultMeasure
                  recipeMeasure .depthFirst registry dismissThenStop false splitState with
              | .ok (.stopped (.policyStop 0) stopped true) =>
                  stopped.choices == 2 && !stopped.session.incomplete &&
                    stopped.session.offers.isEmpty
              | _ => false
          | _ => false

def ageIsSerial : Bool :=
  match controllerRegistry? with
  | none => false
  | some registry =>
      match stateStartWith envelope registry with
      | .error _ => false
      | .ok state =>
          match Controller.runWithin controllerLimits envelope keyCost (fun _ => { bytes := 1 })
              resultMeasure recipeMeasure .depthFirst registry oneThenStop 0 state with
          | .ok (.stopped (.policyStop 1) state 1) =>
              state.session.serial == 1 && state.session.offers.all fun offer =>
                offer.view.age == state.session.serial &&
                  offer.action.serial == state.session.serial
          | _ => false

def stoppingForward : Driver.Package Fact Nat Controller.OfferId Nat (List Nat) :=
  { rule := forwardRule, invoke := fun _ => .stop 7 }

/-- Same-key assembly replacement is a deliberate trusted compatibility
declaration, not callback-body identity. The replacement still crosses the
checked callback and stop-code boundary. -/
def sameKeyReplacementChecked : Bool :=
  let replacement := match packages[0]? with
    | none => #[]
    | some first => packages.set! 0 { first with runtime := stoppingForward }
  match registry?, controllerRegistry? with
  | some proof, some original =>
      match Controller.Registry.buildWithin stateLimits controllerKey program proof replacement with
      | .error _ => false
      | .ok other =>
          match stateStartWith envelope original with
          | .error _ => false
          | .ok state =>
              match Controller.runWithin controllerLimits envelope keyCost unitCost resultMeasure
                  recipeMeasure .depthFirst other firstPolicy () state with
              | .ok (.stopped (.callbackFailure 7) _ _) => true
              | _ => false
  | _, _ => false

#guard providerOneOver
#guard offerOneOver
#guard hugeDraftRejected
#guard hugeBindingRejected
#guard effortOneOver
#guard structuralBatchRejected
#guard emptyNetworkRejected
#guard networkStructuralAccepted
#guard scopedDuplicateInputsRejected
#guard duplicateWritesRejected
#guard duplicateStructuralRejected
#guard repeatControllerAccepted
#guard missingNodeRejected
#guard wrongClassRejected
#guard transplantRejected
#guard matcherEpochRejected
#guard dismissedInvokeIncomplete
#guard dismissedSplitComplete
#guard twoOffersOrdered
#guard dismissThenSelectSticky
#guard restartResetsHandle
#guard stickyClearsAtSplit
#guard ageIsSerial
#guard sameKeyReplacementChecked

def evidence : Proof.Evidence
    (semantics.Entails input.program (Proof.initialBase input) input.target) :=
  match replayRun with
  | .ok evidence => evidence
  | .error _ => Hex.IntervalMathlib.DriverConformance.evidence

theorem controllerCanary :
    semantics.Entails input.program (Proof.initialBase input) input.target :=
  evidence.proof

/--
info: 'Hex.IntervalMathlib.ControllerConformance.controllerCanary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms controllerCanary

end Hex.IntervalMathlib.ControllerConformance
