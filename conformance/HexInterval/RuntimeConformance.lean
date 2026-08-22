/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.RuntimeController

/-!
Conformance for the sealed Mathlib-free typed runtime transition. The fixture
builds the structural shape `sin x = sin (-(-x))` without interpreting sine:
an instance appends two nodes and two scoped applications, an equality admits
their exact descriptor, a fact improves the first node, and transport installs
that fact at the second node. The complete chain runs at a root and in a fresh
split child. A second split after root extension restarts over nonzero assembly
generation, admits the next strict instance, and completes a fresh
equality/fact/transport chain on the new local generation-one suffix.
It also checks that a genuine binary repeated read such as `f x x` remains an
ordered two-slot request across runtime offer generation, Search selection,
and autonomous-controller advancement without admitting stale or spliced
chronology.
-/

namespace Hex.Interval.RuntimeConformance

open Hex.Interval.Runtime Executable Search.Result

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "fixture.source" }
def negKey : OpKey := { name := "fixture.neg" }
def sineKey : OpKey := { name := "fixture.sine" }
def sineNegKey : OpKey := { name := "fixture.sine-neg" }

def instantiateKey : RuleKey := { name := "fixture.sine.instantiate" }
def equalityKey : RuleKey := { name := "fixture.sine.equality" }
def transportKey : RuleKey := { name := "fixture.sine.transport" }
def factKey : RuleKey := { name := "fixture.sine.fact" }

def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def negOperation : Operation := { key := negKey, inputs := [real], output := real }
def sineOperation : Operation := { key := sineKey, inputs := [real], output := real }
def sineNegOperation : Operation := { key := sineNegKey, inputs := [real], output := real }

def program : Program :=
  { operations := #[sourceOperation, negOperation, sineOperation, sineNegOperation]
    nodes :=
      #[{ domain := real, op := { index := 0 }, args := [] },
        { domain := real, op := { index := 1 }, args := [{ index := 0 }] }] }

def extendedProgram : Program :=
  { program with nodes := program.nodes ++
      #[{ domain := real, op := { index := 2 }, args := [{ index := 0 }] },
        { domain := real, op := { index := 3 }, args := [{ index := 1 }] }] }

def twiceExtendedProgram : Program :=
  { extendedProgram with nodes := extendedProgram.nodes ++
      #[{ domain := real, op := { index := 2 }, args := [{ index := 0 }] },
        { domain := real, op := { index := 3 }, args := [{ index := 1 }] }] }

def instantiateRegistration : Registration :=
  { key := instantiateKey, head := negKey, kind := .instantiate,
    watches := [.argument 0], writes := [] }

def equalityRegistration : Registration :=
  { key := equalityKey, head := sineNegKey, kind := .rewrite,
    watches := [], writes := [], binding := .scoped }

def transportRegistration : Registration :=
  { key := transportKey, head := sineNegKey, kind := .rewrite,
    watches := [], writes := [], binding := .scoped }

def factRegistration : Registration :=
  { key := factKey, head := sineKey, kind := .forward,
    watches := [.result], writes := [.result] }

def equalityBinding : ScopeBinding :=
  { rule := equalityKey, anchor := { index := 3 },
    watches := [{ index := 2 }, { index := 3 }], writes := [] }

def transportBinding : ScopeBinding :=
  { rule := transportKey, anchor := { index := 3 },
    watches := [{ index := 2 }], writes := [{ index := 3 }] }

def bindings : Array ScopeBinding := #[equalityBinding, transportBinding]

def nextEqualityBinding : ScopeBinding :=
  { rule := equalityKey, anchor := { index := 5 },
    watches := [{ index := 4 }, { index := 5 }], writes := [] }

def nextTransportBinding : ScopeBinding :=
  { rule := transportKey, anchor := { index := 5 },
    watches := [{ index := 4 }], writes := [{ index := 5 }] }

def nextBindings : Array ScopeBinding :=
  bindings ++ #[nextEqualityBinding, nextTransportBinding]

def instanceQuote : Quote := { role := .instance, schema := 1, body := [11] }
def equalityQuote : Quote := { role := .equality, schema := 2, body := [22] }
def factQuote : Quote := { role := .fact, schema := 3, body := [33] }

def actionFor (request : RuleRequest Nat) : Action := request.action

def instantiateBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  if request.program.nodes.size == program.nodes.size then
    { events := #[.instance
        { action := actionFor request
          after := extendedProgram
          freshFacts := #[30, 40]
          bindings
          newNodes := [{ index := 2 }, { index := 3 }]
          newBindings := [equalityBinding, transportBinding]
          newApplications := [{ index := 1 }, { index := 2 }, { index := 3 }]
          generation := 1
          quote := instanceQuote }] }
  else
    { events := #[.instance
        { action := actionFor request
          after := twiceExtendedProgram
          freshFacts := #[50, 60]
          bindings := nextBindings
          newNodes := [{ index := 4 }, { index := 5 }]
          newBindings := [nextEqualityBinding, nextTransportBinding]
          newApplications := [{ index := 4 }, { index := 5 }, { index := 6 }]
          generation := 2
          quote := instanceQuote }] }

private def endpoint (fallback : Nat) : List SeenVersion → NodeId
  | [] => { index := fallback }
  | seen :: _ => seen.node

def equalityBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  { events := #[.equality
      { action := actionFor request
        equality := { index := 0 }
        left := endpoint 0 request.action.inputs
        right := endpoint 0 request.action.inputs.tail
        generation := request.action.generation
        assumptions := request.action.inputs
        quote := equalityQuote }] }

def factBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  let value := if request.action.node.index == 2 then 31 else 51
  { events := #[.fact
      { action := actionFor request
        update :=
          { programVersion := request.action.programVersion, node := request.action.node,
            previous := { node := request.action.node, version := 0 },
            fact := value, version := 1, cause := 101 }
        proposed := value
        quote := factQuote }] }

def transportBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  let source := request.action.inputs.head?.getD
    { node := request.action.node, version := 0 }
  let value := if request.action.node.index == 3 then 31 else 51
  { events := #[.transport
      { action := actionFor request
        update :=
          { programVersion := request.action.programVersion, node := request.action.node,
            previous := { node := request.action.node, version := 0 },
            fact := value, version := 1, cause := 102 }
        equality := { index := 0 }
        source }] }

def format (role : Role) (schema atom : Nat) : ReplayFormat :=
  { role, schema, validateBody := fun body => body == [atom] }

def handler (registration : Registration) (role : Role) (schema atom : Nat)
    (invoke : RuleRequest Nat → Batch Nat Nat) : Handler Nat (Batch Nat Nat) Unit :=
  { registration
    invoke := fun cache request =>
      ({ result := invoke request,
         quotes := if role == .fact || role == .equality || role == .instance then
           #[{ role, schema, body := [atom] }] else #[] }, cache)
    acceptsScope := fun actual binding =>
      (actual == extendedProgram &&
          (binding == equalityBinding || binding == transportBinding)) ||
        (actual == twiceExtendedProgram &&
          (binding == equalityBinding || binding == transportBinding ||
            binding == nextEqualityBinding || binding == nextTransportBinding))
    formats := if role == .fact || role == .equality || role == .instance then
      #[format role schema atom] else #[] }

def transportHandler : Handler Nat (Batch Nat Nat) Unit :=
  { registration := transportRegistration
    invoke := fun cache request =>
      ({ result := transportBatch request, quotes := #[] }, cache)
    acceptsScope := fun actual binding =>
      (actual == extendedProgram && binding == transportBinding) ||
        (actual == twiceExtendedProgram &&
          (binding == transportBinding || binding == nextTransportBinding))
    formats := #[] }

def runtimePackage : Package Nat (Batch Nat Nat) :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, negOperation, sineOperation, sineNegOperation]
    handlers :=
      #[handler instantiateRegistration .instance 1 11 instantiateBatch,
        handler equalityRegistration .equality 2 22 equalityBatch,
        transportHandler,
        handler factRegistration .fact 3 33 factBatch]
    measure :=
      { metadata := { bytes := 8, work := 8 }
        application := fun _ => { bytes := 1, work := 1 }
        cache := fun _ => {}
        result := fun result =>
          { bytes := result.events.size, work := result.events.size } } }

def packageWith (instanceHandler equalityHandler transportHandler factHandler :
    Handler Nat (Batch Nat Nat) Unit) : Package Nat (Batch Nat Nat) :=
  { runtimePackage with
    handlers := #[instanceHandler, equalityHandler, transportHandler, factHandler] }

/-- A package scheduler may suppress an otherwise executable application. -/
def vetoInstanceHandler : Handler Nat (Batch Nat Nat) Unit :=
  { (handler instantiateRegistration .instance 1 11 instantiateBatch) with
    offers := fun _ request => request.action.kind != .instantiate }

def vetoPackage : Package Nat (Batch Nat Nat) :=
  packageWith vetoInstanceHandler
    (handler equalityRegistration .equality 2 22 equalityBatch)
    transportHandler
    (handler factRegistration .fact 3 33 factBatch)

def splitHandler : Handler Nat (Batch Nat Nat) Unit :=
  handler { instantiateRegistration with kind := .split }
    .instance 1 11 instantiateBatch

def splitPackage : Package Nat (Batch Nat Nat) :=
  packageWith splitHandler
    (handler equalityRegistration .equality 2 22 equalityBatch)
    transportHandler
    (handler factRegistration .fact 3 33 factBatch)

def wrongInstanceBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  { events := #[.instance
      { action := request.action
        after := extendedProgram
        freshFacts := #[30, 40]
        bindings
        newNodes := [{ index := 2 }, { index := 3 }]
        newBindings := [equalityBinding, transportBinding]
        newApplications := [{ index := 1 }, { index := 3 }, { index := 2 }]
        generation := 1
        quote := instanceQuote }] }

def wrongBindingBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  { events := #[.instance
      { action := request.action
        after := extendedProgram
        freshFacts := #[30, 40]
        bindings
        newNodes := [{ index := 2 }, { index := 3 }]
        newBindings := [transportBinding, equalityBinding]
        newApplications := [{ index := 1 }, { index := 2 }, { index := 3 }]
        generation := 1
        quote := instanceQuote }] }

def changedProgram : Program :=
  { extendedProgram with
    nodes := extendedProgram.nodes.set! 1
      { domain := real, op := { index := 0 }, args := [] } }

def wrongProgramBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  { events := #[.instance
      { action := request.action
        after := changedProgram
        freshFacts := #[30, 40]
        bindings
        newNodes := [{ index := 2 }, { index := 3 }]
        newBindings := [equalityBinding, transportBinding]
        newApplications := [{ index := 1 }, { index := 2 }, { index := 3 }]
        generation := 1
        quote := instanceQuote }] }

def wrongGenerationBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  { events := #[.instance
      { action := request.action
        after := extendedProgram
        freshFacts := #[30, 40]
        bindings
        newNodes := [{ index := 2 }, { index := 3 }]
        newBindings := [equalityBinding, transportBinding]
        newApplications := [{ index := 1 }, { index := 2 }, { index := 3 }]
        generation := 0
        quote := instanceQuote }] }

def emptyInstanceBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  { events := #[.instance
      { action := request.action
        after := program
        freshFacts := #[]
        bindings := #[]
        newNodes := []
        newBindings := []
        newApplications := []
        generation := 1
        quote := instanceQuote }] }

def twoEventBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  let events := (instantiateBatch request).events
  { events := events ++ events }

def wrongEqualityBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  { events := #[.equality
      { action := request.action
        equality := { index := 0 }
        left := { index := 2 }
        right := { index := 2 }
        generation := 1
        assumptions := request.action.inputs
        quote := equalityQuote }] }

def wrongOriginBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  { events := #[.equality
      { action := { request.action with serial := 0 }
        equality := { index := 0 }
        left := { index := 2 }
        right := { index := 3 }
        generation := 1
        assumptions := request.action.inputs
        quote := equalityQuote }] }

def wrongAssumptionsBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  { events := #[.equality
      { action := request.action
        equality := { index := 0 }
        left := { index := 2 }
        right := { index := 3 }
        generation := 1
        assumptions := []
        quote := equalityQuote }] }

def wrongEqualityGenerationBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  { events := #[.equality
      { action := request.action
        equality := { index := 0 }
        left := { index := 2 }
        right := { index := 3 }
        generation := 0
        assumptions := request.action.inputs
        quote := equalityQuote }] }

def wrongFactBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  { events := #[.fact
      { action := request.action
        update :=
          { programVersion := 1, node := { index := 3 },
            previous := { node := { index := 3 }, version := 0 },
            fact := 31, version := 1, cause := 101 }
        proposed := 31
        quote := factQuote }] }

def wrongTransportBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  { events := #[.transport
      { action := request.action
        update :=
          { programVersion := 1, node := { index := 3 },
            previous := { node := { index := 3 }, version := 0 },
            fact := 31, version := 1, cause := 102 }
        equality := { index := 1 }
        source := { node := { index := 2 }, version := 1 } }] }

def wrongTransportValueBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  { events := #[.transport
      { action := request.action
        update :=
          { programVersion := request.action.programVersion, node := { index := 3 },
            previous := { node := { index := 3 }, version := 0 },
            fact := 999, version := 1, cause := 102 }
        equality := { index := 0 }
        source := { node := { index := 2 }, version := 1 } }] }

def wrongInstanceHandler : Handler Nat (Batch Nat Nat) Unit :=
  handler instantiateRegistration .instance 1 11 wrongInstanceBatch

def wrongBindingHandler : Handler Nat (Batch Nat Nat) Unit :=
  handler instantiateRegistration .instance 1 11 wrongBindingBatch

def wrongProgramHandler : Handler Nat (Batch Nat Nat) Unit :=
  handler instantiateRegistration .instance 1 11 wrongProgramBatch

def wrongGenerationHandler : Handler Nat (Batch Nat Nat) Unit :=
  handler instantiateRegistration .instance 1 11 wrongGenerationBatch

def emptyInstanceHandler : Handler Nat (Batch Nat Nat) Unit :=
  handler instantiateRegistration .instance 1 11 emptyInstanceBatch

def twoEventHandler : Handler Nat (Batch Nat Nat) Unit :=
  handler instantiateRegistration .instance 1 11 twoEventBatch

def wrongEqualityHandler : Handler Nat (Batch Nat Nat) Unit :=
  handler equalityRegistration .equality 2 22 wrongEqualityBatch

def wrongOriginHandler : Handler Nat (Batch Nat Nat) Unit :=
  handler equalityRegistration .equality 2 22 wrongOriginBatch

def wrongAssumptionsHandler : Handler Nat (Batch Nat Nat) Unit :=
  handler equalityRegistration .equality 2 22 wrongAssumptionsBatch

def wrongEqualityGenerationHandler : Handler Nat (Batch Nat Nat) Unit :=
  handler equalityRegistration .equality 2 22 wrongEqualityGenerationBatch

def wrongFactHandler : Handler Nat (Batch Nat Nat) Unit :=
  handler factRegistration .fact 3 33 wrongFactBatch

def wrongTransportHandler : Handler Nat (Batch Nat Nat) Unit :=
  { transportHandler with invoke := fun cache request =>
      ({ result := wrongTransportBatch request, quotes := #[] }, cache) }

def wrongTransportValueHandler : Handler Nat (Batch Nat Nat) Unit :=
  { transportHandler with invoke := fun cache request =>
      ({ result := wrongTransportValueBatch request, quotes := #[] }, cache) }

def stateLimits : Hex.Interval.State.Limits :=
  { maxOperations := 4, maxNodes := 6, maxRules := 4,
    maxRegistryEntries := 32, maxReplayFormats := 3, maxArity := 1,
    maxScopeNodes := 2, maxApplications := 7, maxQueueEntries := 8,
    maxActions := 8, maxMatcherVisits := 0, matcherBatchSize := 0,
    maxAcceptedFacts := 4, maxRetainedSuggestions := 0, maxEffort := 0,
    maxObservationValue := 8, maxDiagnosticValue := 8,
    maxOutcomeCandidates := 4, maxOutcomeSuggestions := 0,
    maxProposalItems := 0, maxInstances := 1, maxGeneration := 2,
    maxNodeDepth := 2, maxEqualities := 1,
    splitEndpointLimit := { maxEndpointHeight := 8, maxAlignmentShift := 8 } }

def executableLimits : Executable.Limits :=
  { state := stateLimits, maxPackages := 1,
    maxMetadataBytes := 32, maxMetadataWork := 32,
    maxCacheBytes := 0, maxCacheWork := 0,
    maxResultBytes := 1, maxResultWork := 1,
    maxQuotes := 1, maxQuoteCells := 1, maxAtom := 33, maxSchema := 3 }

def limits : Runtime.Limits := { executable := executableLimits, maxEvents := 1 }

def assembly? : Option (Assembly Nat (Batch Nat Nat)) :=
  (Executable.buildWithin executableLimits #[runtimePackage] program).toOption

def assemblyWith? (package : Package Nat (Batch Nat Nat)) :
    Option (Assembly Nat (Batch Nat Nat)) :=
  (Executable.buildWithin executableLimits #[package] program).toOption

def branch? : Option (Hex.Interval.State.Branch Nat Nat) :=
  (Hex.Interval.State.Branch.startWithin stateLimits program #[10, 20]).toOption

def runtime? : Option (Runtime.State Nat Nat) :=
  match assembly?, branch? with
  | some assembly, some branch =>
      (Runtime.State.startWithin limits assembly branch).toOption
  | _, _ => none

def runtimeWith? (package : Package Nat (Batch Nat Nat)) : Option (Runtime.State Nat Nat) :=
  match assemblyWith? package, branch? with
  | some assembly, some branch =>
      (Runtime.State.startWithin limits assembly branch).toOption
  | _, _ => none

#guard assembly?.isSome
#guard branch?.isSome
#guard runtime?.isSome

def action (serial programVersion application rule : Nat) (key : RuleKey)
    (node : Nat) (kind : ActionKind) (generation : Nat)
    (inputs : List SeenVersion) (writes : List NodeId := []) : Action :=
  { serial, programVersion, application := { index := application },
    rule := { index := rule }, key, node := { index := node }, kind,
    effort := 0, generation, inputs, writes }

def instanceAction : Action :=
  action 0 0 0 0 instantiateKey 1 .instantiate 0
    [{ node := { index := 0 }, version := 0 }]

-- `handler.offers` suppresses scheduling but does not grant or revoke runtime
-- execution authority: the snapshot omits this application, while direct
-- checked advancement still reconstructs and executes the exact current row.
#guard runtimeWith? vetoPackage |>.any fun state =>
  match state.offerSnapshotWithin limits 7 with
  | .error _ => false
  | .ok snapshot => snapshot.actions.isEmpty && !snapshot.incomplete &&
      match state.advanceWithin limits 7 instanceAction with
      | .error _ => false
      | .ok advanced => advanced.transition.action == instanceAction &&
          advanced.state.branch.program == extendedProgram

def equalityAction : Action :=
  action 1 1 1 1 equalityKey 3 .rewrite 1
    [{ node := { index := 2 }, version := 0 },
     { node := { index := 3 }, version := 0 }]

def factAction : Action :=
  action 2 1 3 3 factKey 2 .forward 1
    [{ node := { index := 2 }, version := 0 }] [{ index := 2 }]

def transportAction : Action :=
  action 3 1 2 2 transportKey 3 .rewrite 1
    [{ node := { index := 2 }, version := 1 }] [{ index := 3 }]

def run? : Option (Array (Runtime.Applied Nat Nat) × Runtime.State Nat Nat) := do
  let state ← runtime?
  let (instanceStep, state) ← (state.stepWithin limits instanceAction).toOption
  let (equalityStep, state) ← (state.stepWithin limits equalityAction).toOption
  let (factStep, state) ← (state.stepWithin limits factAction).toOption
  let (transportStep, state) ← (state.stepWithin limits transportAction).toOption
  pure (#[instanceStep, equalityStep, factStep, transportStep], state)

#guard run?.any fun result =>
  let state := result.2
  state.branch.program == extendedProgram && state.branch.programVersion == 1 &&
    state.branch.snapshot.facts == #[10, 20, 31, 31] &&
    state.branch.versions == #[0, 0, 1, 1] && state.equalities.size == 1 &&
    state.equalities[0]?.any fun equality =>
      equality.left == { index := 2 } && equality.right == { index := 3 } &&
        equality.generation == 1 && equality.origin == equalityAction

#guard run?.any fun result =>
  match result.1[0]?, result.1[1]? with
  | some instanceStep, some equalityStep =>
      instanceStep.beforeBindings.isEmpty && instanceStep.afterBindings == bindings &&
        instanceStep.beforeApplications.size == 1 &&
        instanceStep.afterApplications.size == 4 &&
        instanceStep.beforeGeneration == 0 && instanceStep.afterGeneration == 1 &&
        instanceStep.beforeEqualities.isEmpty && instanceStep.afterEqualities.isEmpty &&
        equalityStep.beforeBindings == equalityStep.afterBindings &&
        equalityStep.beforeApplications.size == equalityStep.afterApplications.size &&
        equalityStep.beforeGeneration == 1 && equalityStep.afterGeneration == 1 &&
        equalityStep.beforeEqualities.isEmpty && equalityStep.afterEqualities.size == 1
  | _, _ => false

private def runtimeError (actualLimits : Runtime.Limits) (actual : Action) : Option Runtime.Error :=
  match runtime? with
  | none => none
  | some state => match state.stepWithin actualLimits actual with
    | .error error => some error
    | .ok _ => none

#guard runtimeError limits { instanceAction with serial := 1 } == some .stale
#guard runtimeError { limits with executable :=
    { executableLimits with state := { stateLimits with maxActions := 0 } } }
  instanceAction == some (.resource (.state .actions))
#guard runtimeError { limits with maxEvents := 0 } instanceAction ==
  some (.resource .events)
#guard runtimeError { limits with executable :=
    { executableLimits with state := { stateLimits with maxInstances := 0 } } }
  instanceAction == some (.resource (.state .instances))

private def startError (actualLimits : Runtime.Limits) : Option Runtime.Error :=
  match assembly?, branch? with
  | some assembly, some branch => match Runtime.State.startWithin actualLimits assembly branch with
    | .error error => some error
    | .ok _ => none
  | _, _ => none

#guard startError { limits with executable :=
    { executableLimits with state := { stateLimits with maxApplications := 0 } } } ==
  some (.executable (.resource (.state .applications)))

-- A resource rejection returns no cache/state replacement: the same sealed
-- state still accepts the exact action under the original envelope.
#guard runtime?.any fun state =>
  match state.stepWithin { limits with maxEvents := 0 } instanceAction,
      state.stepWithin limits instanceAction with
  | .error (.resource .events), .ok (_, next) => next.serial == 1
  | _, _ => false

private def firstError (package : Package Nat (Batch Nat Nat))
    (actualLimits : Runtime.Limits := limits) : Option Runtime.Error :=
  match runtimeWith? package with
  | none => none
  | some state => match state.stepWithin actualLimits instanceAction with
    | .error error => some error
    | .ok _ => none

private def equalityError (package : Package Nat (Batch Nat Nat))
    (actualLimits : Runtime.Limits := limits) : Option Runtime.Error :=
  match runtimeWith? package with
  | none => none
  | some state => match state.stepWithin limits instanceAction with
    | .error _ => none
    | .ok (_, state) => match state.stepWithin actualLimits equalityAction with
      | .error error => some error
      | .ok _ => none

private def transportError (package : Package Nat (Batch Nat Nat)) : Option Runtime.Error :=
  match runtimeWith? package with
  | none => none
  | some state => match state.stepWithin limits instanceAction with
    | .error _ => none
    | .ok (_, state) => match state.stepWithin limits equalityAction with
      | .error _ => none
      | .ok (_, state) => match state.stepWithin limits factAction with
        | .error _ => none
        | .ok (_, state) => match state.stepWithin limits transportAction with
          | .error error => some error
          | .ok _ => none

private def factError (package : Package Nat (Batch Nat Nat))
    (actualLimits : Runtime.Limits := limits) : Option Runtime.Error :=
  match runtimeWith? package with
  | none => none
  | some state => match state.stepWithin limits instanceAction with
    | .error _ => none
    | .ok (_, state) => match state.stepWithin limits equalityAction with
      | .error _ => none
      | .ok (_, state) => match state.stepWithin actualLimits factAction with
        | .error error => some error
        | .ok _ => none

-- Exact appended application order, equality descriptor endpoints/origin,
-- transport identity, and independent arena/application caps are load-bearing.
#guard firstError (packageWith wrongInstanceHandler
    (handler equalityRegistration .equality 2 22 equalityBatch)
    transportHandler (handler factRegistration .fact 3 33 factBatch)) == some .malformed

#guard firstError (packageWith wrongBindingHandler
    (handler equalityRegistration .equality 2 22 equalityBatch)
    transportHandler (handler factRegistration .fact 3 33 factBatch)) == some .malformed

#guard firstError (packageWith wrongProgramHandler
    (handler equalityRegistration .equality 2 22 equalityBatch)
    transportHandler (handler factRegistration .fact 3 33 factBatch)) ==
  some (.executable .nonExtension)

#guard firstError (packageWith wrongGenerationHandler
    (handler equalityRegistration .equality 2 22 equalityBatch)
    transportHandler (handler factRegistration .fact 3 33 factBatch)) == some .malformed

#guard firstError (packageWith emptyInstanceHandler
    (handler equalityRegistration .equality 2 22 equalityBatch)
    transportHandler (handler factRegistration .fact 3 33 factBatch)) == some .malformed

#guard equalityError (packageWith
    (handler instantiateRegistration .instance 1 11 instantiateBatch)
    wrongEqualityHandler transportHandler
    (handler factRegistration .fact 3 33 factBatch)) == some .wrongEquality

#guard equalityError (packageWith
    (handler instantiateRegistration .instance 1 11 instantiateBatch)
    wrongOriginHandler transportHandler
    (handler factRegistration .fact 3 33 factBatch)) == some .wrongEquality

#guard equalityError (packageWith
    (handler instantiateRegistration .instance 1 11 instantiateBatch)
    wrongAssumptionsHandler transportHandler
    (handler factRegistration .fact 3 33 factBatch)) == some .wrongEquality

#guard equalityError (packageWith
    (handler instantiateRegistration .instance 1 11 instantiateBatch)
    wrongEqualityGenerationHandler transportHandler
    (handler factRegistration .fact 3 33 factBatch)) == some .wrongEquality

#guard factError (packageWith
    (handler instantiateRegistration .instance 1 11 instantiateBatch)
    (handler equalityRegistration .equality 2 22 equalityBatch)
    transportHandler wrongFactHandler) == some .unauthorized

#guard transportError (packageWith
    (handler instantiateRegistration .instance 1 11 instantiateBatch)
    (handler equalityRegistration .equality 2 22 equalityBatch)
    wrongTransportHandler (handler factRegistration .fact 3 33 factBatch)) ==
  some .wrongEquality

#guard transportError (packageWith
    (handler instantiateRegistration .instance 1 11 instantiateBatch)
    (handler equalityRegistration .equality 2 22 equalityBatch)
    wrongTransportValueHandler (handler factRegistration .fact 3 33 factBatch)) ==
  some .unauthorized

#guard equalityError runtimePackage
    { limits with executable :=
      { executableLimits with state := { stateLimits with maxEqualities := 0 } } } ==
  some (.resource (.state .equalities))

#guard runtimeError
    { limits with executable :=
      { executableLimits with state := { stateLimits with maxApplications := 3 } } }
    instanceAction == some (.executable (.resource (.state .applications)))

#guard firstError runtimePackage
    { limits with executable :=
      { executableLimits with state := { stateLimits with maxNodes := 3 } } } ==
  some (.resource (.state .nodes))

#guard firstError runtimePackage
    { limits with executable :=
      { executableLimits with state := { stateLimits with maxGeneration := 0 } } } ==
  some (.resource (.state .generation))

#guard factError runtimePackage
    { limits with executable :=
      { executableLimits with state := { stateLimits with maxAcceptedFacts := 0 } } } ==
  some (.state (.resource .acceptedFacts))

-- The whole returned event count is admitted before the first malformed
-- duplicate could run, even when the executable result envelope is relaxed.
#guard firstError (packageWith twoEventHandler
    (handler equalityRegistration .equality 2 22 equalityBatch)
    transportHandler (handler factRegistration .fact 3 33 factBatch))
    { limits with executable :=
      { executableLimits with maxResultBytes := 2, maxResultWork := 2 } } ==
  some (.resource .events)

/-! # Retained split-child chain -/

def searchLimits : Search.Limits :=
  { maxSteps := 9, maxSplits := 1, maxLeaves := 2, maxFrontier := 2,
    maxDepth := 1, maxScopes := 3, leafFuel := 9 }

def treeLimits : Search.Result.Limits :=
  { search := searchLimits, runtime := limits, maxNodes := 3,
    maxBodyCells := 8, maxBytes := 4096, maxWork := 4096, maxCode := 8 }

def measure : Search.Result.Measure Nat Nat Nat Nat :=
  { node := { bytes := 1, work := 1 }
    branch := fun branch =>
      { bytes := branch.program.nodes.size + branch.history.size + branch.seeds.size,
        work := branch.program.nodes.size + branch.history.size }
    fact := fun _ => { bytes := 1, work := 1 }
    action := fun _ => { bytes := 1, work := 1 }
    plan := fun _ => { bytes := 1, work := 1 }
    schema := fun _ => { bytes := 1, work := 1 }
    body := fun _ => { bytes := 1, work := 1 }
    code := fun _ => { bytes := 1, work := 1 } }

/-! ## Repeated-argument scheduler boundary -/

def repeatKey : OpKey := { name := "fixture.repeat" }
def repeatRuleKey : RuleKey := { name := "fixture.repeat.forward" }

def repeatOperation : Operation :=
  { key := repeatKey, inputs := [real, real], output := real }

/-- A genuine binary `f x x` node resolves two distinct argument slots to the
same source node. Runtime and Search preserve both ordered occurrences with
their exact shared current version. -/
def repeatProgram : Program :=
  { operations := #[sourceOperation, repeatOperation]
    nodes :=
      #[{ domain := real, op := { index := 0 }, args := [] },
        { domain := real, op := { index := 1 }, args := [{ index := 0 }, { index := 0 }] }] }

def repeatRegistration : Registration :=
  { key := repeatRuleKey, head := repeatKey, kind := .forward,
    watches := [.argument 0, .argument 1], writes := [.result] }

private def repeatInputExact (input : FactView Nat) : Bool :=
  input.node == ({ index := 0 } : NodeId) && input.fact == 10 && input.version == 0

def repeatBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  let exactInputs := match request.inputs with
    | [left, right] => repeatInputExact left && repeatInputExact right
    | _ => false
  let value := if exactInputs then 31 else 32
  { events := #[.fact
      { action := request.action
        update :=
          { programVersion := 0, node := { index := 1 },
            previous := { node := { index := 1 }, version := 0 },
            fact := value, version := 1, cause := 103 }
        proposed := value
        quote := factQuote }] }

def repeatPackage : Package Nat (Batch Nat Nat) :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, repeatOperation]
    handlers := #[handler repeatRegistration .fact 3 33 repeatBatch]
    measure := runtimePackage.measure }

def repeatStateLimits : Hex.Interval.State.Limits :=
  { stateLimits with
    maxOperations := 2
    maxNodes := 2
    maxRules := 1
    maxArity := 2
    maxApplications := 1
    maxInstances := 0
    maxGeneration := 0
    maxEqualities := 0 }

def repeatExecutableLimits : Executable.Limits :=
  { executableLimits with state := repeatStateLimits }

def repeatLimits : Runtime.Limits :=
  { executable := repeatExecutableLimits, maxEvents := 1 }

def repeatAssembly? : Option (Assembly Nat (Batch Nat Nat)) :=
  (Executable.buildWithin repeatExecutableLimits #[repeatPackage] repeatProgram).toOption

def repeatBranch? : Option (Hex.Interval.State.Branch Nat Nat) :=
  (Hex.Interval.State.Branch.startWithin repeatStateLimits repeatProgram #[10, 20]).toOption

def repeatRuntime? : Option (Runtime.State Nat Nat) :=
  match repeatAssembly?, repeatBranch? with
  | some assembly, some branch =>
      (Runtime.State.startWithin repeatLimits assembly branch).toOption
  | _, _ => none

def repeatAction : Action :=
  action 0 0 0 0 repeatRuleKey 1 .forward 0
    [{ node := { index := 0 }, version := 0 },
     { node := { index := 0 }, version := 0 }] [{ index := 1 }]

#guard repeatRuntime?.any fun state =>
  match state.stepWithin repeatLimits repeatAction with
  | .ok (_, next) => next.branch.snapshot.facts == #[10, 31]
  | .error _ => false

#guard repeatRuntime?.any fun state =>
  match state.offerSnapshotWithin repeatLimits 1 with
  | .ok snapshot => snapshot.actions == #[repeatAction] && !snapshot.incomplete &&
      snapshot.remaining.actions == 8 && snapshot.remaining.nodes == 0 &&
      snapshot.remaining.applications == 0 && snapshot.remaining.acceptedFacts == 4
  | .error _ => false

/- Distinct declared write slots can also resolve to the same node on `f x x`.
Runtime execution keeps the exact duplicate list and remains sound because the
single emitted fact update is independently checked. Search does not admit
duplicate mutation authority, so offer generation omits the row and reports
the loss through `incomplete`. -/
def repeatWriteRuleKey : RuleKey := { name := "fixture.repeat.write" }

def repeatWriteRegistration : Registration :=
  { key := repeatWriteRuleKey, head := repeatKey, kind := .forward,
    watches := [.result], writes := [.argument 0, .argument 1] }

def repeatWriteBatch (request : RuleRequest Nat) : Batch Nat Nat :=
  let exactWrites := request.writes ==
    [({ index := 0 } : NodeId), ({ index := 0 } : NodeId)]
  let value := if exactWrites then 11 else 12
  { events := #[.fact
      { action := request.action
        update :=
          { programVersion := 0, node := { index := 0 },
            previous := { node := { index := 0 }, version := 0 },
            fact := value, version := 1, cause := 104 }
        proposed := value
        quote := factQuote }] }

def repeatWritePackage : Package Nat (Batch Nat Nat) :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, repeatOperation]
    handlers := #[handler repeatWriteRegistration .fact 3 33 repeatWriteBatch]
    measure := runtimePackage.measure }

def repeatWriteRuntime? : Option (Runtime.State Nat Nat) :=
  match (Executable.buildWithin repeatExecutableLimits #[repeatWritePackage]
      repeatProgram).toOption, repeatBranch? with
  | some assembly, some branch =>
      (Runtime.State.startWithin repeatLimits assembly branch).toOption
  | _, _ => none

def repeatWriteAction : Action :=
  action 0 0 0 0 repeatWriteRuleKey 1 .forward 0
    [{ node := { index := 1 }, version := 0 }] [{ index := 0 }, { index := 0 }]

#guard repeatWriteRuntime?.any fun state =>
  match state.offerSnapshotWithin repeatLimits 1 with
  | .ok snapshot => snapshot.actions.isEmpty && snapshot.incomplete
  | .error _ => false

#guard repeatWriteRuntime?.any fun state =>
  match state.stepWithin repeatLimits repeatWriteAction with
  | .ok (applied, next) =>
      applied.action == repeatWriteAction && next.branch.snapshot.facts == #[11, 20]
  | .error _ => false

def repeatStaleVersion : Action :=
  { repeatAction with inputs :=
      [{ node := { index := 0 }, version := 0 },
       { node := { index := 0 }, version := 1 }] }

def repeatStaleSerial : Action := { repeatAction with serial := 1 }

-- Every repeated read occurrence is checked: one stale version cannot hide
-- behind the current occurrence for the same node.
#guard repeatRuntime?.any fun state =>
  match state.stepWithin repeatLimits repeatStaleVersion with
  | .error .stale => true
  | _ => false

-- Callback chronology remains exact for the newly schedulable action.
#guard repeatRuntime?.any fun state =>
  match state.stepWithin repeatLimits repeatStaleSerial with
  | .error .stale => true
  | _ => false

def splitAction : Action :=
  action 0 0 0 0 instantiateKey 0 .split 0
    [{ node := { index := 0 }, version := 0 }]

def splitRecipe : Search.Result.Split Nat Nat :=
  { scope := { index := 5 }, programVersion := 0, action := splitAction,
    parent := { node := { index := 0 }, version := 0 }, plan := 7,
    schema := 8, body := [1] }

def leftSeed : Search.Result.Seed Nat :=
  { node := { index := 0 }, previous := splitRecipe.parent, fact := 11 }

def rightSeed : Search.Result.Seed Nat :=
  { node := { index := 0 }, previous := splitRecipe.parent, fact := 12 }

def extendedSplitAction : Action :=
  action 4 1 0 0 instantiateKey 0 .split 1
    [{ node := { index := 0 }, version := 0 }]

def extendedSplitRecipe : Search.Result.Split Nat Nat :=
  { scope := { index := 5 }, programVersion := 1, action := extendedSplitAction,
    parent := { node := { index := 0 }, version := 0 }, plan := 7,
    schema := 8, body := [1] }

def extendedLeftSeed : Search.Result.Seed Nat :=
  { node := { index := 0 }, previous := extendedSplitRecipe.parent, fact := 11 }

def extendedRightSeed : Search.Result.Seed Nat :=
  { node := { index := 0 }, previous := extendedSplitRecipe.parent, fact := 12 }

def restartedInstanceAction : Action :=
  action 0 0 0 0 instantiateKey 1 .instantiate 0
    [{ node := { index := 0 }, version := 0 }]

def restartedEqualityAction : Action :=
  action 1 1 4 1 equalityKey 5 .rewrite 2
    [{ node := { index := 4 }, version := 0 },
     { node := { index := 5 }, version := 0 }]

def restartedFactAction : Action :=
  action 2 1 6 3 factKey 4 .forward 2
    [{ node := { index := 4 }, version := 0 }] [{ index := 4 }]

def restartedTransportAction : Action :=
  action 3 1 5 2 transportKey 5 .rewrite 2
    [{ node := { index := 4 }, version := 1 }] [{ index := 5 }]

def splitTree? : Option (Search.Result.Tree Nat Nat Nat Nat) := do
  let branch ← branch?
  let root ← (Search.Result.startWithin treeLimits measure { index := 5 } branch).toOption
  (Search.Result.splitWithin treeLimits measure .depthFirst root splitRecipe leftSeed rightSeed).toOption

def rootTree? : Option (Search.Result.Tree Nat Nat Nat Nat) := do
  let branch ← branch?
  (Search.Result.startWithin treeLimits measure { index := 5 } branch).toOption

private def advanceChild (tree : Search.Result.Tree Nat Nat Nat Nat)
    (state : Runtime.State Nat Nat) : List Action →
    Option (Search.Result.Tree Nat Nat Nat Nat × Runtime.State Nat Nat)
  | [] => some (tree, state)
  | next :: rest =>
      match state.stepWithin limits next with
      | .error _ => none
      | .ok (transition, state) =>
          match Search.Result.advanceRuntimeWithin treeLimits measure tree transition with
          | .error _ => none
          | .ok tree => advanceChild tree state rest

private def childRunFrom (tree : Search.Result.Tree Nat Nat Nat Nat)
    (source : Search.Result.Source Nat Nat)
    (assembly : Assembly Nat (Batch Nat Nat)) :
    Option (Search.Result.Tree Nat Nat Nat Nat × Runtime.State Nat Nat) :=
  match Runtime.State.startWithin limits assembly source.branch with
  | .error _ => none
  | .ok state =>
      advanceChild tree state [instanceAction, equalityAction, factAction, transportAction]

def rootRun? : Option (Search.Result.Tree Nat Nat Nat Nat × Runtime.State Nat Nat) :=
  match rootTree?, assembly? with
  | some tree, some assembly => match Search.Result.current? tree with
    | some (_, source) => childRunFrom tree source assembly
    | none => none
  | _, _ => none

def extendedSplit? : Option
    (Search.Result.Tree Nat Nat Nat Nat × Runtime.State Nat Nat) :=
  match rootRun? with
  | none => none
  | some (tree, state) =>
      match Search.Result.splitWithin treeLimits measure .depthFirst tree
          extendedSplitRecipe extendedLeftSeed extendedRightSeed with
      | .error _ => none
      | .ok tree => some (tree, state)

private def restartedInstanceError (actualLimits : Runtime.Limits) :
    Option Runtime.Error :=
  match extendedSplit? with
  | some (tree, parentState) => match Search.Result.current? tree with
    | some (_, source) =>
        match Runtime.State.startWithin actualLimits parentState.assembly source.branch with
        | .error error => some error
        | .ok state => match state.stepWithin actualLimits restartedInstanceAction with
          | .error error => some error
          | .ok _ => none
    | none => none
  | none => none

def restartRun? : Option (Search.Result.Tree Nat Nat Nat Nat × Runtime.State Nat Nat) :=
  match extendedSplit? with
  | some (tree, parentState) => match Search.Result.current? tree with
    | some (_, source) =>
        match Runtime.State.startWithin limits parentState.assembly source.branch with
        | .error _ => none
        | .ok state => advanceChild tree state
            [restartedInstanceAction, restartedEqualityAction,
              restartedFactAction, restartedTransportAction]
    | none => none
  | none => none

def childRun? : Option (Search.Result.Tree Nat Nat Nat Nat × Runtime.State Nat Nat) :=
  match splitTree?, assembly? with
  | some tree, some assembly => match Search.Result.current? tree with
    | some (_, source) => childRunFrom tree source assembly
    | none => none
  | _, _ => none

#guard rootRun?.any fun result =>
  let tree := result.1
  let state := result.2
  tree.check treeLimits measure && tree.accounting.steps == 4 &&
    state.branch.snapshot.facts == #[10, 20, 31, 31] &&
    match Search.Result.current? tree with
    | some ({ index := 0 }, source) => source.branch == state.branch
    | _ => false

#guard restartRun?.any fun result =>
  let tree := result.1
  let state := result.2
  tree.check treeLimits measure && tree.accounting.steps == 9 &&
    state.generationBase == 1 && state.assembly.generation == 2 &&
    state.branch.programVersion == 1 &&
    state.branch.baseProgram == extendedProgram &&
    state.branch.program == twiceExtendedProgram &&
    state.branch.generations == #[0, 0, 0, 0, 1, 1] &&
    state.branch.snapshot.facts == #[11, 20, 31, 31, 51, 51] &&
    state.equalities.size == 1 &&
    match Search.Result.current? tree with
    | some ({ index := 1 }, source) => source.branch == state.branch
    | _ => false

#guard restartRun?.any fun result =>
  result.1.transitions.size == 8 &&
    result.1.cost == result.1.recomputeCost measure

#guard restartedInstanceError
    { limits with executable :=
      { executableLimits with state := { stateLimits with maxApplications := 6 } } } ==
  some (.executable (.resource (.state .applications)))

#guard restartedInstanceError
    { limits with executable :=
      { executableLimits with state := { stateLimits with maxNodes := 5 } } } ==
  some (.resource (.state .nodes))

#guard restartedInstanceError
    { limits with executable :=
      { executableLimits with state := { stateLimits with maxGeneration := 1 } } } ==
  some (.resource (.state .generation))

#guard restartedInstanceError
    { limits with executable :=
      { executableLimits with state := { stateLimits with maxInstances := 0 } } } ==
  some (.resource (.state .instances))

#guard childRun?.any fun result =>
  let tree := result.1
  let state := result.2
  tree.check treeLimits measure && tree.accounting.steps == 5 &&
    state.branch.snapshot.facts == #[11, 20, 31, 31] &&
    match Search.Result.current? tree with
    | some ({ index := 1 }, source) => source.branch == state.branch
    | _ => false

-- Later retained-tree envelopes re-cap the complete sealed structural tables,
-- event bodies, equality arena, action generations, and caller-declared
-- logical cost. The restarted chain reaches generation two, so one is the
-- exact one-over retained-generation mutation.
#guard restartRun?.any fun result =>
  !result.1.check
    { treeLimits with runtime :=
      { limits with executable :=
        { executableLimits with state := { stateLimits with maxGeneration := 1 } } } } measure

#guard childRun?.any fun result =>
  !result.1.check
    { treeLimits with runtime :=
      { limits with executable :=
        { executableLimits with state := { stateLimits with maxApplications := 3 } } } } measure

#guard childRun?.any fun result =>
  !result.1.check
    { treeLimits with runtime :=
      { limits with executable :=
        { executableLimits with state := { stateLimits with maxEqualities := 0 } } } } measure

#guard childRun?.any fun result =>
  !result.1.check { treeLimits with runtime := { limits with maxEvents := 0 } } measure

#guard childRun?.any fun result =>
  !result.1.check { treeLimits with maxBodyCells := 0 } measure

#guard childRun?.any fun result =>
  0 < result.1.cost.bytes &&
    !result.1.check { treeLimits with maxBytes := result.1.cost.bytes - 1 } measure

#guard childRun?.any fun result =>
  0 < result.1.cost.work &&
    !result.1.check { treeLimits with maxWork := result.1.cost.work - 1 } measure

#guard match rootTree?, run? with
  | some tree, some result =>
      match result.1[0]? with
      | some transition =>
          match Search.Result.advanceRuntimeWithin
              { treeLimits with runtime := { limits with maxEvents := 0 } }
                measure tree transition with
          | .error (.resource .events) => true
          | _ => false
      | none => false
  | _, _ => false

-- Two individually sealed equality transitions with the same branch cannot be
-- spliced: the second must start from the first one's exact equality/table
-- suffix and next serial.
#guard match rootTree?, run? with
  | some tree, some result =>
      match result.1[0]?, result.1[1]? with
      | some instanceStep, some equalityStep =>
          match Search.Result.advanceRuntimeWithin treeLimits measure tree instanceStep with
          | .error _ => false
          | .ok tree =>
              match Search.Result.advanceRuntimeWithin treeLimits measure tree equalityStep with
              | .error _ => false
              | .ok tree =>
                  match Search.Result.advanceRuntimeWithin treeLimits measure tree equalityStep with
                  | .error .malformed => true
                  | _ => false
      | _, _ => false
  | _, _ => false

#guard match splitTree?, run? with
  | some tree, some result =>
      match result.1[0]? with
      | some transition =>
          match Search.Result.advanceRuntimeWithin treeLimits measure tree transition with
          | .error .malformed => true
          | _ => false
      | none => false
  | _, _ => false

/-! # Autonomous sealed typed controller -/

def controllerPolicyLimits : Policy.Limits :=
  { maxOffers := 7, maxBytes := 1024, maxPairs := 32, maxWork := 32,
    maxScore := 0 }

def controllerTraceLimits : Trace.Limit :=
  { maxEvents := 0, maxBytes := 0, maxWork := 0, maxCode := 8 }

def controllerEnvelope : Search.Envelope :=
  { state := stateLimits
    policy := controllerPolicyLimits
    trace := controllerTraceLimits
    search := searchLimits }

def controllerLimits : Runtime.Controller.Limits :=
  { maxChoices := 5, result := treeLimits }

/-- A deterministic conformance policy names only application identities from
the current authenticated offer view. Search returns the retained offer and
reauthenticates its complete fields before Runtime sees its action. -/
def plannedPolicy : Policy.Interface Nat (List Nat) ApplicationId RuleKey :=
  { choose := fun plan view => match plan with
    | [] => .stop []
    | wanted :: rest => match view.offers.find? fun offer => offer.id.index == wanted with
      | none => .stop plan
      | some offer => .select offer rest }

inductive Command where
  | select (application : Nat)
  | dismiss (application : Nat)
  deriving DecidableEq, Repr

/-- Deterministic conformance-only selection/dismissal script. -/
def scriptedPolicy : Policy.Interface Nat (List Command) ApplicationId RuleKey :=
  { choose := fun plan view => match plan with
    | [] => .stop []
    | command :: rest =>
        let wanted := match command with
          | .select application | .dismiss application => application
        match view.offers.find? fun offer => offer.id.index == wanted with
        | none => .stop plan
        | some offer => match command with
          | .select _ => .select offer rest
          | .dismiss _ => .dismiss offer rest }

private def liftOption.{u, v} {α : Type u} (value : Option α) : Option (ULift.{v} α) :=
  value.map ULift.up

def controllerState? : Option (Runtime.Controller.State Nat Nat Nat Nat) := do
  let runtime ← runtime?
  let tree := (← liftOption rootTree?).down
  (Runtime.Controller.State.startWithin controllerLimits controllerEnvelope measure runtime tree).toOption

def splitControllerState? : Option (Runtime.Controller.State Nat Nat Nat Nat) := do
  let runtime ← runtimeWith? splitPackage
  let tree := (← liftOption rootTree?).down
  (Runtime.Controller.State.startWithin controllerLimits controllerEnvelope measure runtime tree).toOption

def repeatTreeLimits : Search.Result.Limits :=
  { treeLimits with runtime := repeatLimits }

def repeatEnvelope : Search.Envelope :=
  { controllerEnvelope with state := repeatStateLimits }

def repeatControllerLimits : Runtime.Controller.Limits :=
  { controllerLimits with result := repeatTreeLimits }

def repeatTree? : Option (Search.Result.Tree Nat Nat Nat Nat) := do
  let branch ← repeatBranch?
  (Search.Result.startWithin repeatTreeLimits measure { index := 5 } branch).toOption

def repeatControllerState? : Option (Runtime.Controller.State Nat Nat Nat Nat) := do
  let runtime ← repeatRuntime?
  let tree := (← liftOption repeatTree?).down
  (Runtime.Controller.State.startWithin repeatControllerLimits repeatEnvelope measure
    runtime tree).toOption

#guard repeatControllerState?.any fun state =>
  state.session.offers.size == 1 && !state.session.incomplete &&
    state.session.offers[0]?.any (fun offer => offer.action == repeatAction) &&
    state.session.remaining.actions == 8 && state.session.remaining.nodes == 0 &&
    match Runtime.Controller.runWithin repeatControllerLimits repeatEnvelope measure
        plannedPolicy [0] state with
    | .ok (.stopped 1 state []) =>
        state.choices == 1 && !state.session.incomplete && state.session.serial == 1 &&
          state.session.offers.size == 1 && state.tree.transitions.size == 1 &&
          state.runtime.branch.snapshot.facts == #[10, 31] &&
          state.session.branch == state.runtime.branch &&
          match Search.Result.current? state.tree with
          | some ({ index := 0 }, source) => source.branch == state.runtime.branch
          | _ => false
    | _ => false

-- Session authentication reaches `actionCurrentChecked` for every retained
-- offer. Replacing only the second repeated occurrence by a stale version
-- invalidates the session before policy selection.
#guard repeatControllerState?.any fun state =>
  let offers := state.session.offers.map fun offer =>
    { offer with action := { offer.action with inputs := repeatStaleVersion.inputs } }
  match Search.Session.refreshWithin repeatEnvelope Runtime.Controller.policyMeasure
      state.session offers state.session.remaining state.session.incomplete with
  | .error .invalidSession => true
  | _ => false

-- The policy echo cannot reuse the repeated-read offer at another callback
-- serial; Search validates chronology before exposing the exact action.
#guard repeatControllerState?.any fun state =>
  match Search.chooseWithin repeatEnvelope Runtime.Controller.policyMeasure
      plannedPolicy [0] state.session with
  | .ok (.select decision _) =>
      match Search.prepareWithin repeatEnvelope Runtime.Controller.policyMeasure
          state.session { decision with serial := 1 } with
      | .error (.policy .staleSerial) => true
      | _ => false
  | _ => false

-- Dismissing the sole ordinary offer removes exactly one live item, charges
-- one decision, and makes the offer view incomplete.
#guard controllerState?.any fun state =>
  match Runtime.Controller.runWithin controllerLimits controllerEnvelope measure
      scriptedPolicy [.dismiss 0] state with
  | .ok (.stopped 0 state []) =>
      state.choices == 1 && state.session.offers.isEmpty && state.session.incomplete
  | _ => false

-- Offer completeness has one meaning: dismissing a live split-class offer is
-- incomplete just like dismissing any other live offer.
#guard splitControllerState?.any fun state =>
  match Runtime.Controller.runWithin controllerLimits controllerEnvelope measure
      scriptedPolicy [.dismiss 0] state with
  | .ok (.stopped 0 state []) =>
      state.choices == 1 && state.session.offers.isEmpty && state.session.incomplete
  | _ => false

-- After one selection creates four live applications, dismissal removes
-- exactly one while preserving the other three.
#guard controllerState?.any fun state =>
  match Runtime.Controller.runWithin controllerLimits controllerEnvelope measure
      scriptedPolicy [.select 0, .dismiss 1] state with
  | .ok (.stopped 3 state []) =>
      state.choices == 2 && state.session.offers.size == 3 &&
        state.session.incomplete &&
        !state.session.offers.any (fun offer => offer.view.id.index == 1)
  | _ => false

-- A later accepted transition regenerates the runtime-owned snapshot, so the
-- dismissed application can reappear; the incompleteness latch stays sticky.
#guard controllerState?.any fun state =>
  match Runtime.Controller.runWithin controllerLimits controllerEnvelope measure
      scriptedPolicy [.select 0, .dismiss 1, .select 3] state with
  | .ok (.stopped _ state []) =>
      state.choices == 3 && state.session.incomplete &&
        state.session.offers.any (fun offer => offer.view.id.index == 1)
  | _ => false

def controllerRun? : Option
    (Runtime.Controller.Run Nat Nat Nat Nat (List Nat)) := do
  let state ← controllerState?
  (Runtime.Controller.runWithin controllerLimits controllerEnvelope measure plannedPolicy
    [0, 1, 3, 2] state).toOption

#guard controllerRun?.any fun run => match run with
  | .stopped _ state [] =>
      state.runtime.branch.program == extendedProgram &&
        state.runtime.branch.programVersion == 1 &&
        state.runtime.branch.snapshot.facts == #[10, 20, 31, 31] &&
        state.runtime.equalities.size == 1 && state.session.serial == 4 &&
        state.session.steps == 4 && state.tree.transitions.size == 4 &&
        state.session.remaining.actions == 4 &&
        state.session.remaining.acceptedFacts == 2 &&
        state.session.remaining.nodes == 2 &&
        state.session.remaining.applications == 3 &&
        state.session.remaining.equalities == 0 &&
        state.session.remaining.instances == 0 &&
        state.session.remaining.queueEntries == 8 &&
        state.session.remaining.generation == 1 &&
        state.tree.check treeLimits measure &&
        match Search.Result.current? state.tree with
        | some ({ index := 0 }, source) => source.branch == state.runtime.branch
        | _ => false
  | _ => false

private def controllerError (actualLimits : Runtime.Controller.Limits)
    (actualEnvelope : Search.Envelope := controllerEnvelope) :
    Option Runtime.Controller.Error :=
  match controllerState? with
  | none => none
  | some state => match Runtime.Controller.runWithin actualLimits actualEnvelope measure
      plannedPolicy [0, 1, 3, 2] state with
    | .error error => some error
    | .ok _ => none

#guard match controllerState? with
  | none => false
  | some state =>
      match Runtime.Controller.runWithin
          { controllerLimits with maxChoices := 4 } controllerEnvelope measure
          plannedPolicy [0, 1, 3, 2] state with
      | .ok (.stopped _ state []) => state.choices == 4
      | _ => false

#guard controllerError { controllerLimits with maxChoices := 3 } ==
  some (.resource .choices)

#guard match runtime?, rootTree? with
  | some runtime, some tree =>
      let envelope := { controllerEnvelope with
        policy := { controllerPolicyLimits with maxOffers := 0 } }
      match Runtime.Controller.State.startWithin controllerLimits envelope measure runtime tree with
      | .error (.runtime (.resource .offers)) => true
      | _ => false
  | _, _ => false

private structure FirstControllerStep where
  initial : Runtime.Controller.State Nat Nat Nat Nat
  decision : Policy.Decision ApplicationId RuleKey
  advanced : Runtime.Advanced Nat Nat
  session : Search.Session Nat Nat ApplicationId RuleKey

private def firstControllerStep? : Option FirstControllerStep := do
  let initial ← controllerState?
  let choice := (← liftOption ((Search.chooseWithin controllerEnvelope
    Runtime.Controller.policyMeasure plannedPolicy [0] initial.session).toOption)).down
  let (Search.Choice.select decision _) := choice | none
  let request := (← liftOption ((Search.prepareWithin controllerEnvelope
    Runtime.Controller.policyMeasure initial.session decision).toOption)).down
  let advanced ← (initial.runtime.advanceWithin limits
    controllerEnvelope.policy.maxOffers request.action).toOption
  let session := (← liftOption ((Search.Session.advanceRuntimeWithin controllerEnvelope
    Runtime.Controller.policyMeasure initial.session decision advanced).toOption)).down
  pure { initial, decision, advanced, session }

-- A consumed decision cannot be replayed at the successor serial.
#guard firstControllerStep?.any fun step =>
  match Search.Session.advanceRuntimeWithin controllerEnvelope
      Runtime.Controller.policyMeasure step.session step.decision step.advanced with
  | .error (.policy .staleSerial) => true
  | _ => false

-- A sealed transition from another runtime lineage cannot be spliced behind
-- a valid repeated-read decision, even though both use the same public
-- application-id type.
#guard match repeatControllerState?, firstControllerStep? with
  | some repeated, some ordinary =>
      match Search.chooseWithin repeatEnvelope Runtime.Controller.policyMeasure
          plannedPolicy [0] repeated.session with
      | .ok (.select decision _) =>
          match Search.Session.advanceRuntimeWithin repeatEnvelope
              Runtime.Controller.policyMeasure repeated.session decision ordinary.advanced with
          | .error .invalidSession => true
          | _ => false
      | _ => false
  | _, _ => false

-- A runtime advanced away from the retained tree head cannot start a new
-- controller lineage, even though both values remain individually sealed.
#guard match runtime?, rootTree? with
  | some runtime, some tree => match runtime.stepWithin limits instanceAction with
    | .error _ => false
    | .ok (_, runtime) =>
        match Runtime.Controller.State.startWithin controllerLimits controllerEnvelope measure
            runtime tree with
        | .error .mismatch => true
        | _ => false
  | _, _ => false

def restartedControllerState? : Option (Runtime.Controller.State Nat Nat Nat Nat) := do
  let (tree, parentRuntime) ← extendedSplit?
  let (_, source) := (← liftOption (Search.Result.current? tree)).down
  let runtime ← (Runtime.State.startWithin limits parentRuntime.assembly source.branch).toOption
  (Runtime.Controller.State.startWithin controllerLimits controllerEnvelope measure runtime tree).toOption

def vetoControllerState? : Option (Runtime.Controller.State Nat Nat Nat Nat) := do
  let runtime ← runtimeWith? vetoPackage
  let tree := (← liftOption rootTree?).down
  (Runtime.Controller.State.startWithin controllerLimits controllerEnvelope measure runtime tree).toOption

-- A decision authenticated against the ordinary package cannot select the
-- same structurally executable application after the scheduler vetoes it.
#guard match controllerState?, vetoControllerState? with
  | some ordinary, some vetoed =>
      match Search.chooseWithin controllerEnvelope Runtime.Controller.policyMeasure
          plannedPolicy [0] ordinary.session with
      | .ok (.select decision _) =>
          vetoed.session.offers.isEmpty &&
            match Search.prepareWithin controllerEnvelope Runtime.Controller.policyMeasure
                vetoed.session decision with
            | .error (.policy .missingOffer) => true
            | _ => false
      | _ => false
  | _, _ => false

-- An offer decision from the root scope cannot be transplanted into a fresh
-- restarted child controller with the same application identity.
#guard match controllerState?, restartedControllerState? with
  | some root, some child =>
      match Search.chooseWithin controllerEnvelope Runtime.Controller.policyMeasure
          plannedPolicy [0] root.session with
      | .ok (.select decision _) =>
          match Search.prepareWithin controllerEnvelope Runtime.Controller.policyMeasure
              child.session decision with
          | .error (.policy .wrongScope) => true
          | _ => false
      | _ => false
  | _, _ => false

def restartedControllerRun? : Option
    (Runtime.Controller.Run Nat Nat Nat Nat (List Nat)) := do
  let state ← restartedControllerState?
  (Runtime.Controller.runWithin controllerLimits controllerEnvelope measure plannedPolicy
    [0, 4, 6, 5] state).toOption

#guard restartedControllerRun?.any fun run => match run with
  | .stopped _ state [] =>
      state.runtime.generationBase == 1 && state.runtime.assembly.generation == 2 &&
        state.runtime.branch.program == twiceExtendedProgram &&
        state.runtime.branch.snapshot.facts == #[11, 20, 31, 31, 51, 51] &&
        state.runtime.equalities.size == 1 && state.session.serial == 4 &&
        state.tree.accounting.steps == 9 && state.tree.transitions.size == 8 &&
        state.tree.check treeLimits measure
  | _ => false

/-- error: Unknown constant `Hex.Interval.Runtime.Applied.mk` -/
#guard_msgs in
#check Runtime.Applied.mk

/-- error: Unknown constant `Hex.Interval.Runtime.Advanced.mk` -/
#guard_msgs in
#check Runtime.Advanced.mk

/-- error: Unknown constant `Hex.Interval.Runtime.OfferSnapshot.mk` -/
#guard_msgs in
#check Runtime.OfferSnapshot.mk

/-- error: Unknown constant `Hex.Interval.Runtime.State.mk` -/
#guard_msgs in
#check Runtime.State.mk

/-- error: Unknown constant `Hex.Interval.Runtime.Controller.State.mk` -/
#guard_msgs in
#check Runtime.Controller.State.mk

/-- error: Unknown constant `Hex.Interval.Runtime.Arena.mk` -/
#guard_msgs in
#check Runtime.Arena.mk

end Hex.Interval.RuntimeConformance
