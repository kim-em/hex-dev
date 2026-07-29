/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.DyadicRules
import HexInterval.Experiment.PolicyDriver

/-!
# Arbitrary-function package conformance

End-to-end conformance for concrete arbitrary-function propagators.  These
fixtures run the generic worklist; they do not call interval operations in
place of the registry when checking the final facts.
-/

namespace Hex.Interval.DyadicRulesConformance

open Experiment Propagator
open DyadicRules

def d (value : Int) : Dyadic := Dyadic.ofInt value

def real : DomainId := { index := 0 }
def sourceOp : OpKey := { name := "real.source" }

def endpointLimit : EndpointLimit where
  maxEndpointHeight := 128
  maxAlignmentShift := 64

def config : Config :=
  { endpointLimit
    reciprocalBasePrecision := 2
    maxReciprocalEffort := 4 }

abbrev ConcreteRegistry := Propagator.Registry Fact

def limits : Experiment.Propagator.Limits :=
  { maxOperations := 16
    maxNodes := 32
    maxRules := 16
    maxArity := 4
    maxApplications := 64
    maxQueueEntries := 256
    maxActions := 128
    maxAcceptedFacts := 128
    maxRetainedSuggestions := 32
    maxEffort := 8
    maxObservationValue := 256
    maxDiagnosticValue := 256
    maxOutcomeCandidates := 4
    maxOutcomeSuggestions := 4
    maxProposalItems := 16
    maxInstances := 8
    maxGeneration := 4
    maxNodeDepth := 16
    maxEqualities := 8
    splitEndpointLimit := endpointLimit }

def registry? : Option ConcreteRegistry :=
  match buildRegistry config real limits with
  | .ok registry => some registry
  | .error _ => none

def allOperations : Array Operation :=
  match registry? with
  | some registry =>
      registry.operations.push { key := sourceOp, inputs := [], output := real }
  | none => #[]

def instruction (operation : Nat) (args : List NodeId := []) : Node :=
  { domain := real, op := { index := operation }, args }

def node (index : Nat) : NodeId := { index }
def suggestion (index : Nat) : SuggestionId := { index }

def finite (lower : Int) (lowerStrict : Bool)
    (upper : Int) (upperStrict : Bool) : Raw :=
  .bounds (.finite (d lower) lowerStrict) (.finite (d upper) upperStrict)

def whole : Raw := .bounds .unbounded .unbounded

def exactFact (state : Engine Fact) (index : Nat) (expected : Raw) : Bool :=
  (state.facts[index]?).any fun fact => fact.view == expected

def registryChecks (program : Program) : Bool :=
  match registry? with
  | some registry => registrationsCheck program registry.registrations
  | none => false

/-! ## Exact backward singleton multiplication -/

/-- Nodes are `2`, `y`, and `z = 2*y`.  The output and input cuts deliberately
mix strict and closed endpoints. -/
def scaleProgram : Program :=
  { operations := allOperations
    nodes :=
      #[instruction 7,
        instruction 7,
        instruction 3 [node 0, node 1]] }

def scaleStart? : Option (Engine Fact × ConcreteRegistry) :=
  match DyadicRules.start config real scaleProgram
      #[finite 2 false 2 false,
        .bounds (.finite 0 true) .unbounded,
        finite 2 true 6 false]
      limits with
  | .ok state => some state
  | .error _ => none

def scaleFinal? : Option (RunResult Fact ConcreteRegistry) := do
  let (state, registry) <- scaleStart?
  pure (drive Propagator.Registry.invoke 32 state registry)

#guard scaleProgram.check
#guard registryChecks scaleProgram

-- The unbounded forward image is honestly inapplicable.  The exact singleton
-- backward contractor nevertheless derives `(1,3]`, then the now-finite
-- forward rule confirms the existing `(2,6]` output.
#guard
  match scaleFinal? with
  | some result =>
      result.stop == .saturated && result.state.metrics.requests == 6 &&
        result.state.metrics.improvements == 1 &&
        result.state.metrics.ruleInapplicable == 4 &&
        exactFact result.state 0 (finite 2 false 2 false) &&
        exactFact result.state 1 (finite 1 true 3 false) &&
        exactFact result.state 2 (finite 2 true 6 false)
  | none => false

/-! ## Mixed forward/backward cycles -/

/-- Three disconnected components exercise negation backward, subtraction
backward-left, and an open square image in one worklist. -/
def cycleProgram : Program :=
  { operations := allOperations
    nodes :=
      #[instruction 7,
        instruction 1 [node 0],
        instruction 7,
        instruction 7,
        instruction 2 [node 3, node 2],
        instruction 7,
        instruction 4 [node 5]] }

def cycleStart? : Option (Engine Fact × ConcreteRegistry) :=
  match DyadicRules.start config real cycleProgram
      #[whole,
        finite 1 false 2 false,
        finite 1 false 2 false,
        whole,
        finite 3 false 4 false,
        finite (-1) true 1 true,
        whole]
      limits with
  | .ok state => some state
  | .error _ => none

def cycleFinal? : Option (RunResult Fact ConcreteRegistry) := do
  let (state, registry) <- cycleStart?
  pure (drive Propagator.Registry.invoke 48 state registry)

#guard cycleProgram.check
#guard registryChecks cycleProgram

#guard
  match cycleFinal? with
  | some result =>
      result.stop == .saturated && !result.state.contradictory &&
        exactFact result.state 0 (finite (-2) false (-1) false) &&
        exactFact result.state 1 (finite 1 false 2 false) &&
        exactFact result.state 2 (finite 1 false 2 false) &&
        exactFact result.state 3 (finite 4 false 6 false) &&
        exactFact result.state 4 (finite 3 false 4 false) &&
        exactFact result.state 5 (finite (-1) true 1 true) &&
        exactFact result.state 6 (finite 0 false 1 true)
  | none => false

/-! ## Dependency loss and centered instantiation -/

/-- `x`, `1`, `1-x`, and `x*(1-x)`. -/
def centeredProgram : Program :=
  { operations := allOperations
    nodes :=
      #[instruction 7,
        instruction 0,
        instruction 2 [node 1, node 0],
        instruction 3 [node 0, node 2]] }

/-! The compact operation table is frontend-owned. Put `source` before the
package-owned centered operation and materialize the centered node already, so
the matcher must resolve its stable key to index seven and CSE-hit node four. -/

def keyedOperations : Array Operation :=
  ((arithmeticOperations real).push
    { key := sourceOp, inputs := [], output := real }).push
      { key := centeredOp, inputs := [real], output := real }

def keyedProgram : Program :=
  { operations := keyedOperations
    nodes :=
      #[instruction 6,
        instruction 0,
        instruction 2 [node 1, node 0],
        instruction 3 [node 0, node 2],
        instruction 7 [node 0]] }

def keyedView : ProgramView :=
  { programVersion := 0
    operations := keyedProgram.operations
    nodes := keyedProgram.nodes
    generations := #[0, 0, 0, 0, 0]
    depths := #[0, 0, 1, 2, 1] }

def keyedRequest : RuleRequest Fact :=
  { action :=
      { serial := 0
        programVersion := 0
        application := { index := 0 }
        rule := { index := 0 }
        key := centeredInstantiateKey
        node := node 3
        kind := .instantiate
        effort := 0
        inputs := [] }
    program := keyedView
    inputs := []
    writes := [] }

def keyedProposal? : Option InstantiationRequest :=
  centeredBinding? keyedRequest >>= centeredProposal? keyedRequest

#guard keyedProgram.check

-- Stable keys resolve to the compact identifier assigned by this particular
-- frontend snapshot; an absent key does not acquire a fallback meaning.
#guard
  match keyedView.findOp? centeredOp with
  | some (operation, signature) =>
      operation.index == 7 && signature.key == centeredOp
  | none => false

#guard
  (keyedView.findOp? { name := "real.absent-from-keyed-view" }).isNone

-- The package uses the resolved identifier in its draft. Structural admission
-- therefore recognizes the already materialized centered node instead of
-- appending a duplicate whose operation index came from package-local order.
#guard
  match keyedProposal? with
  | some proposal =>
      match proposal.nodes with
      | [draft] =>
          draft.op.index == 7 &&
            match resolveDrafts keyedProgram.nodes.size limits.maxNodeDepth
                keyedProgram keyedView.depths [] proposal.nodes with
            | .ok (resolvedProgram, depths, resolved) =>
                resolvedProgram.nodes.size == keyedProgram.nodes.size &&
                  depths == keyedView.depths && resolved == [node 4]
            | .error _ => false
      | _ => false
  | none => false

def centeredStart? : Option (Engine Fact × ConcreteRegistry) :=
  match DyadicRules.start config real centeredProgram
      #[finite 0 false 1 false,
        finite 1 false 1 false,
        whole,
        whole]
      limits with
  | .ok state => some state
  | .error _ => none

def centeredAt (input expected : Dyadic) : Bool :=
  match DyadicInterval.closed endpointLimit input input with
  | .ready fact =>
      match centeredImage endpointLimit fact with
      | .ready image =>
          image.view ==
            .bounds (.finite expected false) (.finite expected false)
      | .inapplicable | .resourceLimit _ => false
  | .inapplicable | .resourceLimit _ => false

def centeredInitial? : Option (RunResult Fact ConcreteRegistry) := do
  let (state, registry) <- centeredStart?
  pure (drive Propagator.Registry.invoke 32 state registry)

def centeredAdmitted? : Option (Engine Fact × ConcreteRegistry) := do
  let initial <- centeredInitial?
  match initial.state.admitInstantiation (suggestion 0) with
  | .admitted [centered] state =>
      if centered == node 4 then
        some (state, initial.cache)
      else
        none
  | _ => none

def centeredFinal? : Option (RunResult Fact ConcreteRegistry) := do
  let (state, registry) <- centeredAdmitted?
  pure (drive Propagator.Registry.invoke 32 state registry)

def falseOneRun? : Option (RunResult Fact ConcreteRegistry) := do
  let (state, registry) <-
    match DyadicRules.start config real centeredProgram
        #[finite 0 false 1 false,
          finite 5 false 5 false,
          whole,
          whole]
        limits with
    | .ok state => some state
    | .error _ => none
  pure (drive Propagator.Registry.invoke 8 state registry)

#guard centeredProgram.check
#guard registryChecks centeredProgram
#guard centeredAt 0 0
#guard centeredAt half quarter
#guard centeredAt 1 0

-- The anchor-local match remains fresh after its own append-only extension.
-- Selecting it again is a structural duplicate, and the matcher is not
-- spuriously requeued as a whole-program dependency.
#guard
  match centeredAdmitted? with
  | some (state, _) =>
      match state.admitInstantiation (suggestion 0) with
      | .duplicate unchanged =>
          unchanged.programVersion == 1 &&
            unchanged.applications.toList.zipIdx.all fun (application, index) =>
              match unchanged.rules[application.rule.index]? with
              | some registration =>
                  registration.key != centeredInstantiateKey ||
                    unchanged.queued[index]? == some false
              | none => false
      | _ => false
  | none => false

def lowEffortLimits : Experiment.Propagator.Limits :=
  { limits with maxEffort := 3 }

def lowDiagnosticLimits : Experiment.Propagator.Limits :=
  { limits with maxDiagnosticValue := 70 }

def noCandidateLimits : Experiment.Propagator.Limits :=
  { limits with maxOutcomeCandidates := 0 }

def noSuggestionLimits : Experiment.Propagator.Limits :=
  { limits with maxOutcomeSuggestions := 0 }

def shortProposalLimits : Experiment.Propagator.Limits :=
  { limits with maxProposalItems := 3 }

def tinySplitLimits : Experiment.Propagator.Limits :=
  { limits with
    splitEndpointLimit := { maxEndpointHeight := 0, maxAlignmentShift := 0 } }

def rejectsPackageLimits (candidateLimits : Experiment.Propagator.Limits) : Bool :=
  match DyadicRules.start config real centeredProgram
      #[finite 0 false 1 false, finite 1 false 1 false, whole, whole]
      candidateLimits with
  | .error .incompatibleLimits => true
  | _ => false

def badSignatureProgram : Program :=
  { centeredProgram with
    operations := centeredProgram.operations.set! 6
      { key := centeredOp, inputs := [real, real], output := real } }

#guard rejectsPackageLimits lowEffortLimits
#guard rejectsPackageLimits lowDiagnosticLimits
#guard rejectsPackageLimits noCandidateLimits
#guard rejectsPackageLimits noSuggestionLimits
#guard rejectsPackageLimits shortProposalLimits
#guard rejectsPackageLimits tinySplitLimits

#guard badSignatureProgram.check
#guard
  match DyadicRules.start config real badSignatureProgram
      #[finite 0 false 1 false, finite 1 false 1 false, whole, whole]
      limits with
  | .error .operationMismatch => true
  | _ => false

-- The distinguished nullary operation carries its own semantics.  A caller
-- cannot seed a node named `real.one` with `{5}` and let the structural
-- identity matcher treat it as one.
#guard
  match falseOneRun? with
  | some result => result.stop == .contradiction && result.state.contradictory
  | none => false

-- Ordinary interval evaluation loses the dependency between the two
-- occurrences of `x` and obtains only `[0,1]`.  The shape rule has no fact
-- inputs, but retains an engine-indexed proposal for the alternate form.
#guard
  match centeredInitial? with
  | some result =>
      result.stop == .saturated && result.state.programVersion == 0 &&
        result.state.suggestions.size == 1 &&
        exactFact result.state 2 (finite 0 false 1 false) &&
        exactFact result.state 3 (finite 0 false 1 false) &&
        match result.state.suggestions[0]? with
        | some retained =>
            retained.action.key == centeredInstantiateKey &&
              retained.action.inputs.isEmpty &&
              match retained.suggestion with
              | .instantiate request =>
                  request.nodes.length == 1 && request.equalities.length == 1
              | _ => false
        | none => false
  | none => false

-- Admission creates the opaque centered node and equality.  Its arbitrary
-- callback returns `[0,1/4]`; equality transport then improves the original
-- product to the same fact. The anchor-local matcher emits no duplicate
-- post-extension suggestion.
#guard
  match centeredFinal? with
  | some result =>
      result.stop == .saturated && result.state.programVersion == 1 &&
        result.state.program.nodes.size == 5 && result.state.equalities.size == 1 &&
        result.state.generations[4]? == some 1 &&
        exactFact result.state 3
          (.bounds (.finite 0 false) (.finite quarter false)) &&
        exactFact result.state 4
          (.bounds (.finite 0 false) (.finite quarter false)) &&
        result.state.suggestions.size == 2 &&
        result.state.suggestions.toList.any (fun retained =>
          retained.action.key == centeredInstantiateKey &&
            retained.action.programVersion == 0) &&
        result.state.suggestions.toList.all (fun retained =>
          retained.action.key != centeredInstantiateKey ||
            retained.action.programVersion == 0) &&
        match result.state.program.node? (node 4), result.state.equalities[0]? with
        | some centered, some equality =>
            centered.args == [node 0] &&
              (result.state.program.operation? centered.op).any
                (fun operation => operation.key == centeredOp) &&
              equality.left == node 3 && equality.right == node 4
        | _, _ => false
  | none => false

/-! ## External policy over concrete function offers -/

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 128
    maxTraversal := 16384
    maxLiveOffers := 512 }

inductive ConcreteCommand
  | invoke (key : RuleKey)
  | instantiate (key : RuleKey)
  | retry (key : RuleKey) (effort : Nat)
  | equality
  | split (key : RuleKey)

def commandMatches (command : ConcreteCommand)
    (offer : Propagator.Policy.OfferView) : Bool :=
  match command, offer.key with
  | .invoke key, .invoke source => source.rule == key
  | .instantiate key, .instantiate source _ => source.rule == key
  | .retry key effort, .retry source offeredEffort =>
      source.rule == key && offeredEffort == effort
  | .equality, .equality _ => true
  | .split key, .split source _ _ _ => source.rule == key
  | _, _ => false

def concreteChoose (commands : List ConcreteCommand)
    (view : Propagator.Policy.View Fact) :
    Propagator.Policy.Driver.Step (List ConcreteCommand) :=
  match commands with
  | [] => .stop []
  | command :: rest =>
      match view.offers.toList.find? (commandMatches command) with
      | none => .stop rest
      | some offer =>
      .select
        { scope := view.scope
          serial := view.serial
          programVersion := view.programVersion
          id := offer.id
          expected := offer.key }
        rest

def concreteController :
    Propagator.Policy.Driver.Controller Fact (List ConcreteCommand) where
  key := { name := "dyadic-rules.script", version := 0 }
  update state _ := state
  choose := concreteChoose

def combinedProgram : Program :=
  { operations := allOperations
    nodes :=
      #[instruction 7,
        instruction 0,
        instruction 2 [node 1, node 0],
        instruction 3 [node 0, node 2],
        instruction 7,
        instruction 5 [node 4]] }

def combinedStart? : Option (Engine Fact × ConcreteRegistry) :=
  match DyadicRules.start config real combinedProgram
      #[finite 0 false 1 false,
        finite 1 false 1 false,
        whole,
        whole,
        finite 3 false 3 false,
        whole]
      limits with
  | .ok state => some state
  | .error _ => none

def concreteCommands : List ConcreteCommand :=
  [.invoke subForwardKey,
    .invoke mulForwardKey,
    .invoke centeredInstantiateKey,
    .instantiate centeredInstantiateKey,
    .invoke centeredSplitKey,
    .invoke centeredForwardKey,
    .equality,
    .invoke reciprocalForwardKey,
    .retry reciprocalForwardKey 1,
    .split centeredSplitKey]

def combinedPolicyRun? : Option
    (Propagator.Policy.Driver.Result Fact ConcreteRegistry
      (List ConcreteCommand)) := do
  let (engine, registry) <- combinedStart?
  let state := Propagator.Policy.State.start engine policyLimits
  pure (Propagator.Policy.Driver.drive concreteController Propagator.Registry.invoke
    32 state registry concreteCommands)

def exactConcreteEvents
    (events : Array (Propagator.Policy.Driver.Event Fact)) : Bool :=
  match events.toList with
  | [.rule _ subObservation,
      .rule _ mulObservation,
      .rule _ instantiateObservation,
      .instance _ (.admitted [fresh]),
      .rule _ splitObservation,
      .rule _ centeredObservation,
      .equality _ equalityObservation,
      .rule _ reciprocalObservation,
      .rule _ retryObservation,
      .splitPrepared _ plan] =>
      subObservation.invocation.rule == subForwardKey &&
        mulObservation.invocation.rule == mulForwardKey &&
        instantiateObservation.invocation.rule == centeredInstantiateKey &&
        fresh == node 6 && splitObservation.invocation.rule == centeredSplitKey &&
        centeredObservation.invocation.rule == centeredForwardKey &&
        equalityObservation.outcome == .improved &&
        reciprocalObservation.invocation.rule == reciprocalForwardKey &&
        reciprocalObservation.invocation.effort == 0 &&
        retryObservation.invocation.rule == reciprocalForwardKey &&
        retryObservation.invocation.effort == 1 &&
        plan.node == node 0 && plan.version == 0
  | _ => false

#guard combinedProgram.check
#guard registryChecks combinedProgram

-- A single external schedule chooses propagation, instantiation, equality,
-- one precision retry, and finally a function-owned split.  The split offer
-- survives unrelated improvements, and retry effort two remains live when the
-- policy deliberately chooses subdivision.  No branch is executed here.
#guard
  match combinedPolicyRun? with
  | some result =>
      result.policyState.isEmpty && result.events.size == 10 &&
        exactConcreteEvents result.events &&
        result.state.metrics.decisions == 10 &&
        result.state.metrics.selectedInvocations == 6 &&
        result.state.metrics.selectedRetries == 1 &&
        result.state.metrics.selectedInstances == 1 &&
        result.state.metrics.selectedSplits == 1 &&
        result.state.metrics.selectedEqualities == 1 &&
        result.state.engine.programVersion == 1 &&
        result.state.engine.program.nodes.size == 7 &&
        result.state.engine.applications.size == 12 &&
        result.state.engine.equalities.size == 1 &&
        result.state.engine.metrics.requests == 7 &&
        result.state.engine.metrics.replies == 7 &&
        result.state.engine.metrics.candidates == 5 &&
        result.state.engine.metrics.improvements == 6 &&
        result.state.engine.metrics.equalityRuns == 1 &&
        result.state.engine.metrics.equalityImprovements == 1 &&
        result.state.engine.versions.toList == [0, 0, 1, 2, 0, 2, 1] &&
        exactFact result.state.engine 3
          (.bounds (.finite 0 false) (.finite quarter false)) &&
        exactFact result.state.engine 5
          (.bounds (.finite quarter true)
            (.finite (Dyadic.ofIntWithPrec 3 3) true)) &&
        exactFact result.state.engine 6
          (.bounds (.finite 0 false) (.finite quarter false)) &&
        (match result.state.offer? (.suggestion (suggestion 3)) with
         | some { key := .retry source 2, .. } =>
             source.rule == reciprocalForwardKey &&
               match result.stop with
               | .split plan =>
                   plan.node == node 0 && plan.version == 0 && plan.point == half &&
                     plan.reason == .criticalPoint &&
                     plan.origin.key == centeredSplitKey &&
                     plan.source.rule == centeredSplitKey &&
                     plan.fact.view == finite 0 false 1 false
               | _ => false
         | _ => false)
  | none => false

/-! ## Retry and malformed dispatch boundaries -/

def reciprocalProgram : Program :=
  { operations := allOperations
    nodes := #[instruction 7, instruction 5 [node 0]] }

def reciprocalStart? : Option (Engine Fact × ConcreteRegistry) :=
  match DyadicRules.start config real reciprocalProgram
      #[finite 3 false 3 false, whole] limits with
  | .ok state => some state
  | .error _ => none

-- Both endpoints of the configured effort range must fit the arithmetic
-- endpoint budget before the package is accepted.
#guard
  match DyadicRules.start
      { config with reciprocalBasePrecision := 129 }
      real reciprocalProgram #[finite 3 false 3 false, whole] limits with
  | .error .incompatibleLimits => true
  | _ => false

#guard
  match DyadicRules.start
      { config with reciprocalBasePrecision := 126, maxReciprocalEffort := 4 }
      real reciprocalProgram #[finite 3 false 3 false, whole] limits with
  | .error .incompatibleLimits => true
  | _ => false

def reciprocalFirstRequest? : Option (RuleRequest Fact × ConcreteRegistry) := do
  let (state, registry) <- reciprocalStart?
  match state.poll with
  | .request request _ => some (request, registry)
  | _ => none

-- Precision two encloses `1/3` by open quarter-grid endpoints and emits the
-- next effort as an advisory retry.
#guard
  match reciprocalFirstRequest? with
  | some (request, registry) =>
      match (registry.invoke request).1 with
      | .success [candidate] [.retry 1] _ =>
          candidate.node == node 1 &&
            candidate.fact.view ==
              .bounds (.finite quarter true) (.finite half true)
      | _ => false
  | none => false

def reciprocalAcrossZeroRequest? : Option (RuleRequest Fact × ConcreteRegistry) := do
  let (state, registry) <- match DyadicRules.start config real reciprocalProgram
      #[finite (-1) false 1 false, whole] limits with
    | .ok state => some state
    | .error _ => none
  match state.poll with
  | .request request _ => some (request, registry)
  | _ => none

-- This first component backend intentionally does not yet implement the
-- connected hull of Lean's total inverse across zero.
#guard
  match reciprocalAcrossZeroRequest? with
  | some (request, registry) =>
      match (registry.invoke request).1 with
      | .inapplicable => true
      | _ => false
  | none => false

def bogusRequest : RuleRequest Fact :=
  { action :=
      { serial := 0
        programVersion := 0
        application := { index := 0 }
        rule := { index := 0 }
        key := { name := "unknown.rule" }
        node := node 0
        kind := .forward
        effort := 0
        inputs := [] }
    program :=
      { programVersion := 0
        operations := #[]
        nodes := #[]
        generations := #[]
        depths := #[] }
    inputs := []
    writes := [] }

-- A callback outside the versioned registry cannot manufacture a candidate;
-- unknown dispatch is a diagnostic failure with no writes.
#guard
  match registry? with
  | some registry =>
      match (registry.invoke bogusRequest).1 with
      | .failed code => code == DispatchCode.requestMismatch
      | _ => false
  | none => false

end Hex.Interval.DyadicRulesConformance
