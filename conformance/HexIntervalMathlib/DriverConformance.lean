/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Driver

/-!
# Authenticated search-to-proof driver conformance

The live canary accepts one root improvement, splits that updated root, accepts
one child-local improvement, closes the left target, and refutes the right
child.  Every retained proof event is returned by the same package invocation
as its runtime command; the driver never reconstructs recipes from causes.
-/

namespace Hex.IntervalMathlib.DriverConformance

open Hex.Interval
open Hex.Interval.Proof

inductive Fact where
  | all | yes | empty
  deriving DecidableEq, Repr

def domain : DomainId := { index := 0 }
def sourceKey : OpKey := { name := "driver-source", version := 1 }
def operation : Operation := { key := sourceKey, inputs := [], output := domain }
def sourceNode : Node := { domain, op := { index := 0 }, args := [] }
def n0 : NodeId := { index := 0 }
def n1 : NodeId := { index := 1 }
def n2 : NodeId := { index := 2 }
def n3 : NodeId := { index := 3 }
def program : Program :=
  { operations := #[operation], nodes := #[sourceNode, sourceNode, sourceNode, sourceNode] }

#guard program.check

def scope : Policy.ScopeId := { index := 20 }
def leftScope : Policy.ScopeId := { index := 21 }
def rightScope : Policy.ScopeId := { index := 22 }
def seen (node : NodeId) (version : Nat) : SeenVersion := { node, version }

def contains : Fact → Bool → Prop
  | .all, _ => True
  | .yes, value => value = true
  | .empty, _ => False

def semantics : Proof.Semantics Fact :=
  { Value := Bool
    models := fun checked valuation =>
      checked = program ∧ valuation n0 = valuation n1 ∧ valuation n1 = valuation n2 ∧
        valuation n2 = valuation n3
    holds := fun _ valuation fact => contains fact.fact (valuation fact.node)
    holdsAgree := by
      intro checked left right fact within _ _ agree
      rw [agree fact.node within] }

def factDomain : Proof.Domain semantics :=
  { top := fun _ => .all
    topSound := by simp [semantics, contains]
    meet := fun checked node previous proposed installed =>
      if shape : (previous = .all ∨ previous = .yes) ∧ proposed = .yes ∧
          installed = .yes then
        some
          { proof := by
              rcases shape with ⟨previousShape, rfl, rfl⟩
              rcases previousShape with rfl | rfl
              · intro valuation model
                simp [semantics, contains]
              · intro valuation model
                simp [semantics, contains] }
      else none }

theorem laws : Proof.Laws semantics :=
  { holdsEq := by
      intro checked valuation left right fact model equal
      simp only [semantics, contains]
      rw [equal] }

def forwardRule : RuleKey := { name := "driver-forward", schema := 1 }
def splitRule : RuleKey := { name := "driver-split", schema := 1 }
def refuteRule : RuleKey := { name := "driver-refute", schema := 1 }

def forwardRegistration : Registration :=
  { key := forwardRule, head := sourceKey, kind := .forward,
    watches := [], writes := [], binding := .scoped }
def splitRegistration : Registration :=
  { key := splitRule, head := sourceKey, kind := .split,
    watches := [], writes := [], binding := .scoped }
def refuteRegistration : Registration :=
  { key := refuteRule, head := sourceKey, kind := .backward,
    watches := [], writes := [], binding := .scoped }
def registrations : Array Registration :=
  #[forwardRegistration, splitRegistration, refuteRegistration]

def factKey : Proof.Key := { rule := forwardRule, role := .fact, bodySchema := 1 }
def splitKey : Proof.Key := { rule := splitRule, role := .split, bodySchema := 2 }
def refuteKey : Proof.Key := { rule := refuteRule, role := .refute, bodySchema := 3 }

def decode (expected : Nat) (body : List Nat) : Option Unit :=
  if body = [expected] then some () else none

def factSchema : Proof.FactSchema semantics :=
  { key := factKey
    Certificate := Unit
    decode := decode 11
    prove := fun context _ =>
      if rootShape : context.scope = scope ∧ context.program = program ∧
          context.proposed = { node := n2, fact := .yes } ∧
          context.assumptions = [{ node := n1, fact := .yes }] then
        some
          { proof := by
              rcases rootShape with ⟨_, programEq, proposedEq, assumptionsEq⟩
              intro valuation model assumptions
              have source := assumptions { node := n1, fact := .yes } (by
                simp [assumptionsEq])
              rw [proposedEq]
              simpa [semantics, contains, programEq, model.2.2.1] using source }
      else if childShape : context.scope = leftScope ∧ context.program = program ∧
          context.proposed = { node := n3, fact := .yes } ∧
          context.assumptions = [{ node := n0, fact := .yes }] then
        some
          { proof := by
              rcases childShape with ⟨_, programEq, proposedEq, assumptionsEq⟩
              intro valuation model assumptions
              have source := assumptions { node := n0, fact := .yes } (by
                simp [assumptionsEq])
              rw [proposedEq]
              simpa [semantics, contains, programEq, model.2.1, model.2.2.1,
                model.2.2.2] using source }
      else none }

def splitSchema : Proof.SplitSchema semantics (List Nat) :=
  { key := splitKey
    Certificate := Unit
    decode := decode 22
    prove := fun context _ =>
      if shape : context.scope = scope ∧ context.programVersion = 0 ∧
          context.program = program ∧
          { node := n1, fact := .yes } ∈ context.assumptions ∧
          context.parent = { node := n0, fact := .all } ∧
          context.left = { node := n0, fact := .yes } ∧
          context.right = { node := n0, fact := .empty } ∧ context.plan = [22] then
        some
          { proof := by
              rcases shape with ⟨_, _, _, sourceMember, _, leftEq, _, _⟩
              intro valuation model assumptions
              left
              have source := assumptions { node := n1, fact := .yes } sourceMember
              simpa [leftEq, semantics, contains, model.2.1] using source }
      else none }

def refuteSchema : Proof.RefuteSchema semantics :=
  { key := refuteKey
    Certificate := Unit
    decode := decode 33
    prove := fun context _ =>
      if shape : context.scope = rightScope ∧ context.program = program ∧
          context.fact = .empty then
        some
          { proof := by
              rcases shape with ⟨_, _, factEq⟩
              intro valuation model impossible
              rw [factEq] at impossible
              exact impossible }
      else none }

def package : Proof.Package semantics (List Nat) :=
  { registrations, facts := #[factSchema], splits := #[splitSchema],
    refuters := #[refuteSchema] }

def proofLimits : Proof.Limits :=
  { maxPackages := 1, maxSchemas := 3, maxBodyCells := 1,
    maxDependencies := 2, maxChronology := 2 }

def registry? : Option (Proof.Registry semantics (List Nat)) :=
  (Proof.Registry.buildWithin proofLimits program #[package]).toOption

def input : Proof.Input Fact :=
  { scope, program, facts := #[.all, .yes, .all, .all],
    target := { node := n3, fact := .yes } }

def stateLimits : State.Limits :=
  { maxOperations := 1, maxNodes := 4, maxRules := 3,
    maxRegistryEntries := 3, maxReplayFormats := 3, maxArity := 2,
    maxScopeNodes := 2, maxApplications := 4, maxQueueEntries := 4,
    maxActions := 8, maxMatcherVisits := 0, matcherBatchSize := 0,
    maxAcceptedFacts := 2, maxRetainedSuggestions := 4, maxEffort := 1,
    maxObservationValue := 4, maxDiagnosticValue := 8,
    maxOutcomeCandidates := 1, maxOutcomeSuggestions := 0, maxProposalItems := 2,
    maxInstances := 0, maxGeneration := 1, maxNodeDepth := 0, maxEqualities := 0,
    splitEndpointLimit := { maxEndpointHeight := 8, maxAlignmentShift := 8 } }

def searchLimits : Search.Limits :=
  { maxSteps := 5, maxSplits := 1, maxLeaves := 2, maxFrontier := 2,
    maxDepth := 1, maxScopes := 3, leafFuel := 4 }

def policyLimits : Policy.Limits :=
  { maxOffers := 1, maxBytes := 32, maxPairs := 16, maxWork := 32, maxScore := 4 }

def envelope : Search.Envelope :=
  { state := stateLimits, policy := policyLimits,
    trace := { maxEvents := 4, maxBytes := 32, maxWork := 32, maxCode := 8 },
    search := searchLimits }

def policyMeasure : Policy.Measure Nat Nat :=
  { id := fun _ => { bytes := 1, pairs := 0, work := 1 },
    key := fun _ => { bytes := 1, pairs := 0, work := 1 } }

def unitCost : Search.Result.Cost := { bytes := 1, work := 1 }
def resultMeasure : Search.Result.Measure Fact Nat (List Nat) Proof.Key :=
  { node := unitCost
    branch := fun branch =>
      { bytes := branch.snapshot.facts.size + branch.history.size,
        work := branch.versions.size + branch.history.size }
    fact := fun _ => unitCost, action := fun _ => unitCost, plan := fun _ => unitCost,
    schema := fun _ => unitCost, body := fun _ => unitCost, code := fun _ => unitCost }

def resultLimits : Search.Result.Limits :=
  { search := searchLimits, state := stateLimits, maxNodes := 3, maxBodyCells := 1,
    maxBytes := 128, maxWork := 128, maxCode := 8 }

def treeLimits : Proof.TreeLimits :=
  { maxNodes := 3, maxDepth := 1, maxBodyCells := 6, maxWork := 32 }

def limits : Driver.Limits := { result := resultLimits, proof := proofLimits, tree := treeLimits }

def binding (rule : RuleKey) (anchor : NodeId) (watches writes : List NodeId) :
    ScopeBinding := { rule, anchor, watches, writes }

def action (serial application rule : Nat) (key : RuleKey) (kind : ActionKind)
    (node : NodeId) (inputs : List SeenVersion) (writes : List NodeId) : Action :=
  { serial, programVersion := 0, application := { index := application }, rule := { index := rule },
    key, node, kind, effort := 0, generation := 0, inputs, writes }

def offer (id : Nat) (kind : ActionKind) (action : Action) :
    Search.Offer Nat Nat :=
  { view := { id, key := id, offerClass :=
      match kind with | .split => .split | _ => .invoke, age := 0, score := 0 }, action }

def choose? (session : Search.Session Fact Nat Nat Nat) : Option (Policy.Decision Nat Nat) := do
  let selected ← session.view.offers[0]?
  pure (Policy.select session.view selected)

def update (request : Search.Request Fact Nat Nat) (node : NodeId)
    (previous : SeenVersion) (fact : Fact) (version cause : Nat) : State.Update Fact Nat :=
  { programVersion := request.programVersion, node, previous, fact, version, cause }

def factEvent (request : Search.Request Fact Nat Nat) (update : State.Update Fact Nat) :
    Proof.Event Fact :=
  .fact
    { scope := request.scope, programVersion := request.programVersion, action := request.action,
      node := update.node, previous := update.previous, version := update.version,
      proposed := update.fact, installed := update.fact, assumptions := request.action.inputs,
      schema := factKey, body := [11] }

def outcome (request : Search.Request Fact Nat Nat) (items : Array (State.Update Fact Nat)) :
    Search.Outcome Fact Nat Nat Nat :=
  { scope := request.scope
    serial := request.serial
    programVersion := request.programVersion
    offer := request.offer
    action := request.action
    updates := items }

def rootPackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { rule := forwardRule
    invoke := fun request =>
      let item := update request n2 (seen n2 0) .yes 1 1
      .continue (Driver.Echo.mk (outcome request (Array.singleton item))
        [factEvent request item]) }

def splitPackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { rule := splitRule
    invoke := fun request =>
      .split
        { echo := Driver.Echo.mk (outcome request #[]) []
          runtime :=
            { scope := request.scope, programVersion := request.programVersion,
              action := request.action, parent := seen n0 0, plan := [22],
              schema := splitKey, body := [22] }
          left := { node := n0, previous := seen n0 0, fact := .yes }
          right := { node := n0, previous := seen n0 0, fact := .empty } } }

def childPackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { rule := forwardRule
    invoke := fun request =>
      let item := update request n3 (seen n3 0) .yes 1 2
      .continue (Driver.Echo.mk (outcome request (Array.singleton item))
        [factEvent request item]) }

def targetPackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { rule := forwardRule
    invoke := fun request => .target (Driver.Echo.mk (outcome request #[]) [])
      { scope := request.scope, programVersion := request.programVersion, seen := seen n3 1 } }

def refutePackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { rule := refuteRule
    invoke := fun request => .refute (Driver.Echo.mk (outcome request #[]) [])
      { scope := request.scope, programVersion := request.programVersion, seen := seen n0 0,
        schema := refuteKey, body := [33] } }

def badOwnerPackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { rootPackage with rule := splitRule }

def badDependencyPackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { rule := forwardRule
    invoke := fun request =>
      let item := update request n2 (seen n2 0) .yes 1 1
      let event := factEvent request item
      .continue (Driver.Echo.mk (outcome request (Array.singleton item))
        [match event with | .fact step => .fact { step with assumptions := [] } | other => other]) }

def badSchemaPackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { rule := forwardRule
    invoke := fun request =>
      let item := update request n2 (seen n2 0) .yes 1 1
      let event := factEvent request item
      .continue (Driver.Echo.mk (outcome request (Array.singleton item))
        [match event with | .fact step => .fact { step with schema := splitKey } | other => other]) }

def badEchoPackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { rule := forwardRule
    invoke := fun request =>
      let item := update request n2 (seen n2 0) .yes 1 1
      let echo := { outcome request (Array.singleton item) with serial := request.serial + 1 }
      .continue (Driver.Echo.mk echo [factEvent request item]) }

def stoppingPackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { rule := forwardRule, invoke := fun _ => .stop 7 }

def unknownPackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { rule := forwardRule
    invoke := fun request => .unknown (Driver.Echo.mk (outcome request #[]) [])
      { scope := request.scope, programVersion := request.programVersion, code := 1 } }

def badSplitSchemaPackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { splitPackage with invoke := fun request =>
      match splitPackage.invoke request with
      | .split split => .split { split with runtime := { split.runtime with schema := factKey } }
      | command => command }

def staleSplitSeedPackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { splitPackage with invoke := fun request =>
      match splitPackage.invoke request with
      | .split split => .split { split with left := { split.left with previous := seen n0 1 } }
      | command => command }

def badSplitPlanPackage : Driver.Package Fact Nat Nat Nat (List Nat) :=
  { splitPackage with invoke := fun request =>
      match splitPackage.invoke request with
      | .split split => .split { split with runtime := { split.runtime with plan := [23] } }
      | command => command }

def rootAction := action 0 0 0 forwardRule .forward n2 [seen n1 0] [n2]
def splitAction := action 1 1 1 splitRule .split n0 [seen n1 0, seen n0 0] []
def childAction := action 0 2 0 forwardRule .forward n3 [seen n0 0] [n3]
def targetAction := action 1 3 0 forwardRule .forward n3 [seen n3 1] [n3]
def refuteAction := action 0 2 2 refuteRule .backward n0 [seen n0 0] []

def rootBindings : Array ScopeBinding :=
  #[binding forwardRule n2 [n1] [n2], binding splitRule n0 [n1, n0] []]
def leftBindings : Array ScopeBinding :=
  #[binding forwardRule n3 [n0] [n3], binding forwardRule n3 [n3] [n3]]
def rightBindings : Array ScopeBinding := #[binding refuteRule n0 [n0] []]

def makeSession (branch : State.Branch Fact Nat) (scope : Policy.ScopeId)
    (bindings : Array ScopeBinding) (selected : Search.Offer Nat Nat) :=
  Search.Session.startWithin envelope policyMeasure branch registrations bindings #[0, 0, 0, 0]
    #[] 0 scope #[selected]

def firstWith (package : Driver.Package Fact Nat Nat Nat (List Nat))
    (candidateLimits : Driver.Limits := limits) : Option (Driver.Step Fact Nat Nat Nat (List Nat)) := do
  let branch ← (State.Branch.startWithin stateLimits program input.facts).toOption
  let bundle ← (Driver.Bundle.startWithin candidateLimits resultMeasure scope branch).toOption
  let session ← (makeSession branch scope rootBindings (offer 0 .forward rootAction)).toOption
  let decision ← choose? session
  (Driver.runWithin envelope policyMeasure candidateLimits resultMeasure .depthFirst package
    bundle session decision).toOption

#guard match firstWith rootPackage with | some (.continued _ _) => true | _ => false
#guard (firstWith badOwnerPackage).isNone
#guard (firstWith badDependencyPackage).isNone
#guard (firstWith badSchemaPackage).isNone
#guard (firstWith badEchoPackage).isNone
#guard match firstWith stoppingPackage with
  | some (.stopped (.callbackFailure 7) bundle session) =>
      session.serial == 0 && bundle.tree.pending.length == 1
  | _ => false
#guard match firstWith unknownPackage with | some (.unknown _) => true | _ => false
#guard (firstWith rootPackage { limits with proof := { proofLimits with maxChronology := 0 } }).isNone
#guard (firstWith rootPackage { limits with result := { resultLimits with maxNodes := 0 } }).isNone

def staleAction := { rootAction with generation := 1 }
#guard match State.Branch.startWithin stateLimits program input.facts with
  | .ok branch => match makeSession branch scope rootBindings
      (offer 0 .forward staleAction) with
    | .error _ => true
    | .ok _ => false
  | .error _ => false

def splitWith (package : Driver.Package Fact Nat Nat Nat (List Nat)) :
    Option (Driver.Step Fact Nat Nat Nat (List Nat)) := do
  let branch ← (State.Branch.startWithin stateLimits program input.facts).toOption
  let bundle ← (Driver.Bundle.startWithin limits resultMeasure scope branch).toOption
  let session ← (makeSession branch scope rootBindings (offer 0 .forward rootAction)).toOption
  let decision ← choose? session
  let .continued bundle session ← (Driver.runWithin envelope policyMeasure limits resultMeasure
    .depthFirst rootPackage bundle session decision).toOption | none
  let session ← (Search.Session.refreshWithin envelope policyMeasure session
    #[offer 1 .split splitAction] {} false).toOption
  let decision ← choose? session
  (Driver.runWithin envelope policyMeasure limits resultMeasure .depthFirst package
    bundle session decision).toOption

#guard match splitWith splitPackage with | some (.split _) => true | _ => false
#guard (splitWith badSplitSchemaPackage).isNone
#guard (splitWith staleSplitSeedPackage).isNone

private def orCode (code : Nat) (result : Except ε α) : Except Nat α :=
  result.mapError fun _ => code

private def driverCode (base : Nat) : Driver.Error → Nat
  | .search _ => base + 1
  | .result _ => base + 2
  | .proof _ => base + 3
  | .mismatch => base + 4

private def runWith
    (selectedSplit : Driver.Package Fact Nat Nat Nat (List Nat)) :
    Except Nat (Driver.Bundle Fact Nat (List Nat) ×
    Search.Result.Tree Fact Nat (List Nat) Proof.Key × Proof.TreeRecipe Fact) := do
  let branch ← orCode 1 (State.Branch.startWithin stateLimits program input.facts)
  let bundle ← orCode 2 (Driver.Bundle.startWithin limits resultMeasure scope branch)
  let session ← orCode 3 (makeSession branch scope rootBindings
    (offer 0 .forward rootAction))
  let some decision := choose? session | throw 4
  let step ← orCode 5 (Driver.runWithin envelope policyMeasure limits resultMeasure .depthFirst
    rootPackage bundle session decision)
  let .continued bundle session := step | throw 6
  let session ← orCode 7 (Search.Session.refreshWithin envelope policyMeasure session
    #[offer 1 .split splitAction] {} false)
  let some decision := choose? session | throw 8
  let step ← orCode 9 (Driver.runWithin envelope policyMeasure limits resultMeasure .depthFirst
    selectedSplit bundle session decision)
  let .split bundle := step | throw 10
  let some (_, left) := Search.Result.current? bundle.tree | throw 11
  let session ← orCode 12 (makeSession left.branch left.scope leftBindings
    (offer 2 .forward childAction))
  let some decision := choose? session | throw 13
  let step ← (Driver.runWithin envelope policyMeasure limits resultMeasure .depthFirst
    childPackage bundle session decision).mapError (driverCode 140)
  let .continued bundle session := step | throw 15
  let session ← orCode 16 (Search.Session.refreshWithin envelope policyMeasure session
    #[offer 3 .forward targetAction] {} false)
  let some decision := choose? session | throw 17
  let step ← orCode 18 (Driver.runWithin envelope policyMeasure limits resultMeasure .depthFirst
    targetPackage bundle session decision)
  let .terminal bundle := step | throw 19
  let some (_, right) := Search.Result.current? bundle.tree | throw 20
  let session ← orCode 21 (makeSession right.branch right.scope rightBindings
    (offer 4 .backward refuteAction))
  let some decision := choose? session | throw 22
  let step ← orCode 23 (Driver.runWithin envelope policyMeasure limits resultMeasure .depthFirst
    refutePackage bundle session decision)
  let .terminal bundle := step | throw 24
  pure (bundle, bundle.tree, bundle.recipe)

private def runE := runWith splitPackage

def run? := runE.toOption

def replayRun := do
  let some (_, tree, recipe) := run? | throw Proof.Error.wrongTree
  let some registry := registry? | throw Proof.Error.invalidInput
  Proof.replayTree resultLimits resultMeasure proofLimits treeLimits registry
    factDomain laws input tree recipe

private def replayWithSplit (selectedSplit : Driver.Package Fact Nat Nat Nat (List Nat)) := do
  let (_, tree, recipe) ← runWith selectedSplit
  let some registry := registry? | throw 25
  (Proof.replayTree resultLimits resultMeasure proofLimits treeLimits registry
    factDomain laws input tree recipe).mapError fun _ => 26

private def changeRootBody (recipe : Proof.TreeRecipe Fact) : Option (Proof.TreeRecipe Fact) := do
  let events ← recipe.events[0]?
  let event ← events.head?
  let changed := match event with
    | .fact step => Proof.Event.fact { step with body := [12] }
    | other => other
  pure { recipe with events := recipe.events.set! 0 (changed :: events.drop 1) }

private def changeLeftSide (recipe : Proof.TreeRecipe Fact) : Option (Proof.TreeRecipe Fact) := do
  let edge ← recipe.edges[1]?
  pure { recipe with edges := recipe.edges.set! 1 { edge with side := some .right } }

private def replayMutated
    (change : Proof.TreeRecipe Fact → Option (Proof.TreeRecipe Fact)) := do
  let (_, tree, recipe) ← runE.mapError fun _ => Proof.Error.wrongTree
  let some changed := change recipe | throw Proof.Error.wrongTree
  let some registry := registry? | throw Proof.Error.invalidInput
  Proof.replayTree resultLimits resultMeasure proofLimits treeLimits registry
    factDomain laws input tree changed

#guard runE.isOk
#guard replayRun.isOk
#guard match replayWithSplit badSplitPlanPackage with | .error 26 => true | _ => false
#guard match replayMutated changeRootBody with | .error .malformedBody => true | _ => false
#guard match replayMutated changeLeftSide with | .error .wrongTree => true | _ => false

def evidence : Proof.Evidence
    (semantics.Entails input.program (Proof.initialBase input) input.target) :=
  match replayRun with
  | .ok evidence => evidence
  | .error _ =>
      { proof := by
          intro valuation model assumptions
          have source := assumptions { node := n1, fact := .yes } (by
            simp [Proof.initialBase, input, n1])
          simpa [semantics, contains, input, n3, model.2.2.1, model.2.2.2] using source }

theorem driverCanary :
    semantics.Entails input.program (Proof.initialBase input) input.target :=
  evidence.proof

/--
info: 'Hex.IntervalMathlib.DriverConformance.driverCanary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms driverCanary

end Hex.IntervalMathlib.DriverConformance
