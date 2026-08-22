/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Driver
public import HexInterval.Executable

@[expose] public section

/-!
# Bounded autonomous package controller

This module aligns a stable table of package-owned application generators with
both the supported runtime driver and an exact supported proof registry.  An
application generator may inspect the current authenticated branch, but it
cannot choose its compact application/rule identity, serial, program version,
or dependency generations: the controller reconstructs those fields and
`Search.Session` authenticates the resulting action before a policy can see it.

The controller deterministically enumerates the table, asks a replaceable
policy to select or dismiss one of the already-authenticated offers, invokes
the exactly aligned runtime package, and repeats over the sealed retained tree.
Runtime callbacks, generator callbacks, policy callbacks, equality on caller
types, and logical measurement callbacks remain non-preemptible.  Their
results are revalidated before retention, and a caller-owned logical measure
bounds every retained policy-state successor after its non-preemptible
construction.  The controller never creates proof evidence; its untrusted bundle must still cross
`Proof.replayTree` with an independently checked proof registry from the same
trusted compatibility epoch. Runtime registry object identity is not required.

`maxChoices` and non-split dismissal incompleteness are cumulative only within
one returned sealed `State` lineage. `State.startWithin` deliberately starts a
new handle from any sealed current bundle: it resets choices, the dismissal
latch, and the search session's serial, steps, and trace even when the retained
head and scope are unchanged. Pure Lean values may be reused to explore
alternative bounded successors. This is not a global or process-persistent
budget, nor does restarting inherit any proof-closure or saturation claim.

This is the supported autonomous programmatic loop. Goal reification and the
public tactic currently use the separate flat forward path; split-search tactic
integration remains a later edge. The current runtime driver accepts fact
events only. The explicit `Controller.Package` route above still uses toy
fact-event callbacks and application generators in conformance; it has no
concrete built-in arithmetic driver package. The `Executable` namespace below
is the distinct route by which built-in arithmetic and independently owned
arbitrary-function fact packages reach this controller: it adapts a sealed
Mathlib-free executable assembly without a caller application table.
Equality/instance actions, program-extension discovery, and automatic package
discovery remain later interfaces.
-/

namespace Hex.Interval.Controller

open Proof

variable {Fact Cause SemanticKey Plan PolicyState : Type}

/-- Stable compatibility declaration for one explicit runtime/proof assembly.
Assemblies built with the same key are deliberately treated as interchangeable
trusted implementations of that epoch; the key is not object identity or a
hash of Lean callback bodies. Callback results remain fully revalidated. -/
structure Key where
  name : String
  version : Nat
  deriving DecidableEq, Repr

/-- Stable policy identity for one slot in the exact application table. -/
abbrev OfferId := ApplicationId

/-- Package-generated policy metadata and action ports.  Identity, rule,
chronology, age, and dependency generations are controller-owned. Every offer
in one immutable snapshot receives that snapshot's single session serial as its
age. A malformed draft aborts generation transactionally; no prefix is
retained. -/
structure Draft (SemanticKey : Type) where
  key : SemanticKey
  offerClass : Policy.OfferClass
  score : Int := 0
  node : NodeId
  effort : Nat
  inputs : List NodeId
  writes : List NodeId := []
  structuralInputs : List StructuralKey := []

/-- One stable application slot.  `binding` is consulted on every branch and
must remain unchanged during updates within one scope.  `offer` may return
`none` when the application is currently inapplicable.  Both callbacks are
non-preemptible; all returned lists are capped before traversal. -/
structure Application (Fact Cause SemanticKey : Type) where
  generation : Nat := 0
  binding : Policy.ScopeId → State.Branch Fact Cause → Option ScopeBinding := fun _ _ => none
  offer : Policy.ScopeId → State.Branch Fact Cause → Option (Draft SemanticKey)

/-- One exact fact-event rule owns one runtime callback and a deterministic
application suffix.  Proof schemas remain in the separately built
`Proof.Registry`; this is explicit assembly, not automatic discovery. -/
structure Package (Fact Cause SemanticKey Plan : Type) where
  runtime : Driver.Package Fact Cause OfferId SemanticKey Plan
  applications : Array (Application Fact Cause SemanticKey)

/-- Independent logical caps for one retained policy-state value. Measurement
and construction of the arbitrary caller type remain non-preemptible. -/
structure PolicyLimit where
  bytes : Nat
  pairs : Nat
  work : Nat
  deriving DecidableEq, Repr

/-- Bounds specific to application enumeration and autonomous policy choices.
All state, policy, search, result-tree, proof, and recipe bounds remain in the
supported envelopes passed to the transitions. `maxChoices` applies to one
sealed `State` lineage; explicit `State.startWithin` creates a new lineage and
resets it together with the dismissal latch and search-session chronology. -/
structure Limits where
  maxChoices : Nat
  policyState : PolicyLimit
  driver : Driver.Limits
  deriving DecidableEq, Repr

/-- Controller-owned resource refusals. `narrow budget` preserves the exact
budget reported by `NarrowResult.resourceLimit`; unlike `mismatch` or a
fixed-point `noChange`, it says the fact domain refused attempted work and no
update was retained. -/
inductive Resource where
  | applications
  | choices
  | policyState
  | state (resource : State.Resource)
  | narrow (budget : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | invalidRegistry
  | invalidApplication (application : ApplicationId)
  | resource (resource : Resource)
  | search (error : Search.Error)
  | driver (error : Driver.Error)
  | mismatch
  deriving DecidableEq, Repr

private def liftCheck.{u} (result : Except Error Unit) : Except Error PUnit.{u + 1} :=
  match result with
  | .error error => .error error
  | .ok _ => .ok PUnit.unit

/-- Ordinary-import-sealed alignment of one program, theorem registry, runtime
packages, and deterministic application table. -/
structure Registry (Fact : Type) (semantics : Proof.Semantics Fact)
    (Cause SemanticKey Plan : Type) where
  private mk ::
  key : Key
  program : Program
  proof : Proof.Registry semantics Plan
  packages : Array (Package Fact Cause SemanticKey Plan)
  applications : Array (RuleId × Application Fact Cause SemanticKey)
  applicationGenerations : Array Nat
  equalityGenerations : Array Nat
  matcherEpoch : Nat

private def flattenWithin (limit : Nat)
    (packages : Array (Package Fact Cause SemanticKey Plan)) :
    Except Error (Array (RuleId × Application Fact Cause SemanticKey)) := do
  let mut applications := #[]
  for ruleIndex in [0:packages.size] do
    let some package := packages[ruleIndex]? | throw .invalidRegistry
    for application in package.applications do
      if limit ≤ applications.size then throw (.resource .applications)
      applications := applications.push ({ index := ruleIndex }, application)
  pure applications

private def preflightProgram (limits : State.Limits) (program : Program) :
    Except Error Unit := do
  if limits.maxOperations < program.operations.size then
    throw (.resource (.state .operations))
  if limits.maxNodes < program.nodes.size then throw (.resource (.state .nodes))
  if program.operations.any (fun operation =>
      !Search.listWithin limits.maxArity operation.inputs) ||
      program.nodes.any (fun node => !Search.listWithin limits.maxArity node.args) then
    throw (.resource (.state .arity))

private def preflightRegistrations (limits : State.Limits)
    (registrations : Array Registration) : Except Error Unit := do
  if limits.maxRules < registrations.size then throw (.resource (.state .rules))
  for registration in registrations do
    let portLimit := match registration.binding with
      | .local => limits.maxArity + 1
      | .scoped => limits.maxScopeNodes
      | .global => 0
    if !Search.listWithin portLimit registration.watches ||
        !Search.listWithin portLimit registration.writes then
      throw (.resource (.state (if registration.binding == .scoped then .scopes else .arity)))

private def preflightBranch (limits : State.Limits) (branch : State.Branch Fact Cause) :
    Except Error Unit := do
  preflightProgram limits branch.baseProgram
  preflightProgram limits branch.program
  if limits.maxAcceptedFacts < branch.history.size then
    throw (.resource (.state .acceptedFacts))
  if limits.maxNodes < branch.initialFacts.size || limits.maxNodes < branch.seeds.size ||
      limits.maxNodes < branch.versions.size || limits.maxNodes < branch.generations.size ||
      limits.maxNodes < branch.depths.size then
    throw (.resource (.state .nodes))
  if branch.depths.any (fun depth => limits.maxNodeDepth < depth) then
    throw (.resource (.state .nodeDepth))
  if branch.generations.any (fun generation => limits.maxGeneration < generation) then
    throw (.resource (.state .generation))

/-- Build one exact runtime/proof package alignment.  Runtime package order is
the proof registration order, so a compact `RuleId` resolves to the same
stable key on both sides. -/
opaque Registry.buildWithin
    (stateLimits : State.Limits) (key : Key) (program : Program)
    (proof : Proof.Registry semantics Plan)
    (packages : Array (Package Fact Cause SemanticKey Plan))
    (equalityGenerations : Array Nat := #[]) (matcherEpoch : Nat := 0) :
    Except Error (Registry Fact semantics Cause SemanticKey Plan) := do
  if stateLimits.maxRules < packages.size ||
      stateLimits.maxRules < proof.registrations.size then
    throw (.resource (.state .rules))
  if stateLimits.maxRegistryEntries < packages.size then
    throw (.resource (.state .registryEntries))
  if stateLimits.maxEqualities < equalityGenerations.size then
    throw (.resource (.state .equalities))
  liftCheck (preflightProgram stateLimits program)
  liftCheck (preflightRegistrations stateLimits proof.registrations)
  if proof.registrations.size != packages.size then
    throw .invalidRegistry
  if stateLimits.maxGeneration < matcherEpoch ||
      equalityGenerations.any (fun generation => stateLimits.maxGeneration < generation) then
    throw (.resource (.state .generation))
  for index in [0:packages.size] do
    let some package := packages[index]? | throw .invalidRegistry
    let some registration := proof.registrations[index]? | throw .invalidRegistry
    if package.runtime.rule != registration.key then throw .invalidRegistry
  match flattenWithin stateLimits.maxApplications packages with
  | .error error => throw error
  | .ok applications =>
      let generations := applications.map (·.2.generation)
      if generations.any (fun generation => stateLimits.maxGeneration < generation) then
        throw (.resource (.state .generation))
      if !program.check || !Registration.check program proof.registrations then
        throw .invalidRegistry
      pure
        { key, program, proof, packages, applications,
          applicationGenerations := generations, equalityGenerations, matcherEpoch }

private def structuralGeneration?
    (registry : Registry Fact semantics Cause SemanticKey Plan)
    (branch : State.Branch Fact Cause) : StructuralKey → Option Nat
  | .node node => branch.generations[node.index]?
  | .application application => registry.applicationGenerations[application.index]?
  | .equality equality => registry.equalityGenerations[equality.index]?

private def seenInputs? (branch : State.Branch Fact Cause)
    (nodes : List NodeId) : Option (List SeenVersion) :=
  nodes.mapM fun node => do
    let version ← branch.versions[node.index]?
    pure { node, version }

private def structuralInputs?
    (registry : Registry Fact semantics Cause SemanticKey Plan)
    (branch : State.Branch Fact Cause) (keys : List StructuralKey) :
    Option (List StructuralInput) :=
  keys.mapM fun key => do
    let generation ← structuralGeneration? registry branch key
    pure { key, generation }

private def offerClass (kind : ActionKind) : Policy.OfferClass :=
  match kind with
  | .split => .split
  | .instantiate => .instantiate
  | .improve | .shave | .regularize => .retry
  | _ => .invoke

private structure Generated (OfferId SemanticKey : Type) where
  offers : Array (Search.Offer OfferId SemanticKey)
  bindings : Array ScopeBinding

private def generate [DecidableEq Fact] [DecidableEq Cause]
    (envelope : Search.Envelope)
    (registry : Registry Fact semantics Cause SemanticKey Plan)
    (branch : State.Branch Fact Cause) (scope : Policy.ScopeId) (serial : Nat) :
    Except Error (Generated OfferId SemanticKey) := do
  preflightBranch envelope.state branch
  if !branch.check then throw .mismatch
  if branch.program != registry.program then throw .mismatch
  let mut offers := #[]
  let mut bindings := #[]
  for index in [0:registry.applications.size] do
    let applicationId : ApplicationId := { index }
    let some (ruleId, application) := registry.applications[index]?
      | throw (.invalidApplication applicationId)
    let some registration := registry.proof.registrations[ruleId.index]?
      | throw (.invalidApplication applicationId)
    let binding := application.binding scope branch
    let draft := application.offer scope branch
    match registration.binding, binding, draft with
    | .scoped, some exact, _ =>
        if !Search.listWithin envelope.state.maxScopeNodes exact.watches ||
            !Search.listWithin envelope.state.maxScopeNodes exact.writes then
          throw (.resource (.state .scopes))
        if exact.rule != registration.key then throw (.invalidApplication applicationId)
        if !bindings.contains exact then
          if envelope.state.maxApplications ≤ bindings.size then
            throw (.resource .applications)
          bindings := bindings.push exact
    | .scoped, none, none => pure ()
    | .local, none, _ | .global, none, _ => pure ()
    | _, _, _ => throw (.invalidApplication applicationId)
    let some draft := draft | continue
    let portLimit := match registration.binding with
      | .local => envelope.state.maxArity + 1
      | .scoped => envelope.state.maxScopeNodes
      | .global => 0
    let portResource := if registration.binding == .scoped then State.Resource.scopes
      else State.Resource.arity
    if !Search.listWithin portLimit draft.inputs ||
        !Search.listWithin portLimit draft.writes then
      throw (.resource (.state portResource))
    if !Search.listWithin envelope.state.matcherBatchSize draft.structuralInputs then
      throw (.resource (.state .matcherVisits))
    if envelope.state.maxEffort < draft.effort then
      throw (.resource (.state .effort))
    /- Draft reads are ordered occurrences. Distinct local registration slots
    may resolve to one node, and `seenInputs?` preserves every occurrence for
    exact Search authentication. Scoped reads and all write/structural
    authority remain distinct. -/
    if (registration.binding == .scoped && !allDistinct draft.inputs) ||
        !allDistinct draft.writes || !allDistinct draft.structuralInputs then
      throw (.invalidApplication applicationId)
    if (branch.program.node? draft.node).isNone ||
        draft.writes.any (fun node => (branch.program.node? node).isNone) then
      throw (.invalidApplication applicationId)
    let matcherValid := match registration.matchWatch with
      | .none => draft.structuralInputs.isEmpty
      | .network => !draft.structuralInputs.isEmpty
    if !matcherValid then throw (.invalidApplication applicationId)
    let some inputs := seenInputs? branch draft.inputs
      | throw (.invalidApplication applicationId)
    let some structuralInputs := structuralInputs? registry branch draft.structuralInputs
      | throw (.invalidApplication applicationId)
    if draft.offerClass != offerClass registration.kind then
      throw (.invalidApplication applicationId)
    let action : Action :=
      { serial, programVersion := branch.programVersion, application := applicationId,
        rule := ruleId, key := registration.key, node := draft.node,
        kind := registration.kind, effort := draft.effort,
        generation := application.generation, inputs, writes := draft.writes,
        structuralInputs,
        matcherEpoch := if registration.matchWatch == .network
          then some registry.matcherEpoch else none }
    let view : Policy.OfferView OfferId SemanticKey :=
      { id := applicationId, key := draft.key, offerClass := draft.offerClass,
        age := serial, score := draft.score }
    if envelope.policy.maxOffers ≤ offers.size then
      throw (.search (.policy .offerLimit))
    offers := offers.push { view, action }
  pure { offers, bindings }

/-- Compose the controller-owned application identifier cost with a
caller-owned semantic-key measure. -/
def policyMeasure (key : SemanticKey → Policy.Cost) :
    Policy.Measure OfferId SemanticKey :=
  { id := fun id => { bytes := id.index + 1, work := 1 }, key }

private def checkPolicyWithin (limits : PolicyLimit)
    (measure : PolicyState → Policy.Cost) (state : PolicyState) : Except Error Unit := do
  let cost := measure state
  if limits.bytes < cost.bytes || limits.pairs < cost.pairs || limits.work < cost.work then
    throw (.resource .policyState)

private def startSession [DecidableEq Fact] [DecidableEq Cause]
    (envelope : Search.Envelope) (measure : Policy.Measure OfferId SemanticKey)
    (registry : Registry Fact semantics Cause SemanticKey Plan)
    (scope : Policy.ScopeId) (branch : State.Branch Fact Cause) :
    Except Error (Search.Session Fact Cause OfferId SemanticKey) := do
  let generated ← generate envelope registry branch scope 0
  Search.Session.startWithin envelope measure branch registry.proof.registrations
    generated.bindings registry.applicationGenerations registry.equalityGenerations
    registry.matcherEpoch scope generated.offers |>.mapError Error.search

private def refresh [DecidableEq Fact] [DecidableEq Cause]
    (envelope : Search.Envelope) (measure : Policy.Measure OfferId SemanticKey)
    (registry : Registry Fact semantics Cause SemanticKey Plan)
    (session : Search.Session Fact Cause OfferId SemanticKey)
    (dismissedIncomplete : Bool) :
    Except Error (Search.Session Fact Cause OfferId SemanticKey) := do
  let generated ← generate envelope registry session.branch session.scope session.serial
  if generated.bindings != session.bindings then throw .mismatch
  Search.Session.refreshWithin envelope measure session generated.offers {}
    dismissedIncomplete
    |>.mapError Error.search

/-- Sealed live alignment of a retained runtime/proof bundle, its declared
registry compatibility epoch, exact current session, and cumulative
policy-choice accounting. `dismissedIncomplete` is sticky for the current
scope within this returned state lineage: accepting another action cannot erase
an earlier non-split dismissal. Explicit `State.startWithin` creates a new
lineage and resets it even when it starts from the same retained head. -/
structure State (Fact Cause OfferId SemanticKey Plan : Type) where
  private mk ::
  compatibility : Key
  bundle : Driver.Bundle Fact Cause Plan
  session : Search.Session Fact Cause OfferId SemanticKey
  choices : Nat
  dismissedIncomplete : Bool

/-- Start a new autonomous-controller handle at the exact current retained-tree
head. This explicit operation resets the per-lineage choice counter and
dismissal latch and rebuilds a search session with serial zero, zero accepted
steps, and an empty diagnostic trace. The retained bundle head and scope may be
the same as an older handle; the new handle does not inherit that handle's
incompleteness, proof-closure, or saturation status. -/
opaque State.startWithin [DecidableEq Fact] [DecidableEq Cause]
    (envelope : Search.Envelope) (measure : Policy.Measure OfferId SemanticKey)
    (registry : Registry Fact semantics Cause SemanticKey Plan)
    (bundle : Driver.Bundle Fact Cause Plan) :
    Except Error (State Fact Cause OfferId SemanticKey Plan) := do
  let some (_, source) := Search.Result.current? bundle.tree | throw .mismatch
  let session ← startSession envelope measure registry source.scope source.branch
  pure
    { compatibility := registry.key, bundle, session, choices := 0,
      dismissedIncomplete := false }

private def nextState [DecidableEq Fact] [DecidableEq Cause]
    (envelope : Search.Envelope) (measure : Policy.Measure OfferId SemanticKey)
    (registry : Registry Fact semantics Cause SemanticKey Plan)
    (bundle : Driver.Bundle Fact Cause Plan) (choices : Nat) :
    Except Error (Option (State Fact Cause OfferId SemanticKey Plan)) := do
  match Search.Result.current? bundle.tree with
  | none => pure none
  | some (_, source) =>
      let session ← startSession envelope measure registry source.scope source.branch
      pure (some
        { compatibility := registry.key, bundle, session, choices,
          dismissedIncomplete := false })

private def runtime?
    (registry : Registry Fact semantics Cause SemanticKey Plan) (id : OfferId) :
    Option (Driver.Package Fact Cause OfferId SemanticKey Plan) := do
  let (rule, _) ← registry.applications[id.index]?
  let package ← registry.packages[rule.index]?
  let registration ← registry.proof.registrations[rule.index]?
  if package.runtime.rule == registration.key then
    pure package.runtime
  else none

/-- Controller termination. `complete` means only that the sealed runtime tree
has no pending frontier; it is not proof closure or evidence. The retained tree
and recipe must still pass `Proof.replayTree`. -/
inductive Run (Fact Cause OfferId SemanticKey Plan PolicyState : Type)
  | complete (bundle : Driver.Bundle Fact Cause Plan) (policy : PolicyState)
  | stopped (stop : Search.Stop Unit Unit)
      (state : State Fact Cause OfferId SemanticKey Plan) (policy : PolicyState)
  | unknown (bundle : Driver.Bundle Fact Cause Plan) (policy : PolicyState)

/-- Run deterministic offer regeneration and replaceable policy selection until
the retained tree closes, honestly stops, reaches an unknown leaf, or exhausts
the cumulative choice cap.  Dismissal removes exactly one offer from the
current immutable snapshot. Dismissing a non-split offer marks that snapshot
incomplete; dismissing a split probe does not. Within one returned state
lineage, that incompleteness survives accepted refreshes in the same scope and
clears when a split or terminal transition moves to the next retained scope.
Explicit `State.startWithin` creates a new lineage and resets the latch even at
the same retained head. A policy stop returns a resumable sealed state, whereas
choice-cap exhaustion is a resource error. `policyStateMeasure`
is non-preemptible, but its declared byte, pair, and work cost must fit before
the initial state or any callback successor is retained. In the reference
implementation, choice authenticates the entry session; each selected driver
step validates the current and replacement retained bundles/trees, and the
regenerated session is authenticated again. Thus total reference validation
cost scales linearly with the choice cap as well as with these repeated
session and retained-tree validation passes. -/
opaque runWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq SemanticKey]
    [DecidableEq Plan]
    (limits : Limits) (envelope : Search.Envelope)
    (keyMeasure : SemanticKey → Policy.Cost)
    (policyStateMeasure : PolicyState → Policy.Cost)
    (resultMeasure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (recipeMeasure : Driver.Measure Fact) (order : Search.Order)
    (registry : Registry Fact semantics Cause SemanticKey Plan)
    (policy : Policy.Interface Fact PolicyState OfferId SemanticKey)
    (policyState : PolicyState)
    (initial : State Fact Cause OfferId SemanticKey Plan) :
    Except Error (Run Fact Cause OfferId SemanticKey Plan PolicyState) := do
  if initial.compatibility != registry.key then throw .mismatch
  checkPolicyWithin limits.policyState policyStateMeasure policyState
  let measure := policyMeasure keyMeasure
  let rec loop (fuel : Nat) (state : State Fact Cause OfferId SemanticKey Plan)
      (policyState : PolicyState) :
      Except Error (Run Fact Cause OfferId SemanticKey Plan PolicyState) := do
    if state.choices >= limits.maxChoices then throw (.resource .choices)
    match fuel with
    | 0 => throw (.resource .choices)
    | fuel + 1 =>
      let choice ← Search.chooseWithin envelope measure policy policyState state.session
        |>.mapError Error.search
      match choice with
      | .stopped stop next =>
          checkPolicyWithin limits.policyState policyStateMeasure next
          pure (.stopped stop state next)
      | .dismiss decision next =>
          checkPolicyWithin limits.policyState policyStateMeasure next
          let offers := state.session.offers.filter fun offer => offer.view.id != decision.id
          if offers.size + 1 != state.session.offers.size then throw .mismatch
          let dismissedIncomplete :=
            state.dismissedIncomplete || decision.offerClass != .split
          let session ← Search.Session.refreshWithin envelope measure state.session offers
            state.session.remaining dismissedIncomplete |>.mapError Error.search
          loop fuel
            { state with session, choices := state.choices + 1, dismissedIncomplete } next
      | .select decision next =>
          checkPolicyWithin limits.policyState policyStateMeasure next
          let some package := runtime? registry decision.id | throw .mismatch
          let step ← Driver.runWithin envelope measure limits.driver resultMeasure recipeMeasure
            order package state.bundle state.session decision |>.mapError Error.driver
          let choices := state.choices + 1
          match step with
          | .continued bundle session =>
              let session ← refresh envelope measure registry session state.dismissedIncomplete
              loop fuel
                { compatibility := state.compatibility, bundle, session, choices,
                  dismissedIncomplete := state.dismissedIncomplete } next
          | .split bundle | .terminal bundle =>
              match ← nextState envelope measure registry bundle choices with
              | none => pure (.complete bundle next)
              | some state => loop fuel state next
          | .unknown bundle => pure (.unknown bundle next)
          | .stopped stop bundle session =>
              pure (.stopped stop
                { compatibility := state.compatibility, bundle, session, choices,
                  dismissedIncomplete := state.dismissedIncomplete } next)
  loop limits.maxChoices initial policyState

/-! ## Sealed executable-assembly adapter -/

namespace Executable

/-- One package proposal. All chronology, current facts, installed meets, and
action data are deliberately absent: the adapter derives them from the
authenticated search request and its checked runtime fact domain. -/
structure Proposal (Fact Cause : Type) where
  node : NodeId
  proposed : Fact
  cause : Cause

/-- The only callback result admitted by the current executable adapter.
Every update must have exactly one separately returned raw quotation. -/
structure FactOutcome (Fact Cause : Type) where
  proposals : Array (Proposal Fact Cause)
  diagnostic : Option Trace.Event := none

abbrev RawAssembly (Fact Cause : Type) :=
  Hex.Interval.Executable.Assembly Fact (FactOutcome Fact Cause)

/-- Exact executable/theorem alignment. The executable assembly supplies the
program, flattened registrations, routes, applications, callbacks, and private
caches; callers cannot provide a second application or runtime table. -/
structure Registry (Fact : Type) (semantics : Proof.Semantics Fact)
    (Cause Plan : Type) where
  private mk ::
  key : Controller.Key
  assembly : RawAssembly Fact Cause
  domain : FactDomain Fact
  proof : Proof.Registry semantics Plan
  applicationGenerations : Array Nat
  matcherEpoch : Nat

inductive Error where
  | invalidRegistry
  | invalidApplication (application : ApplicationId)
  | invalidQuote
  | missingSchema (key : Proof.Key)
  | invalidBody (key : Proof.Key)
  | resource (resource : Controller.Resource)
  | search (error : Search.Error)
  | driver (error : Driver.Error)
  | executable (error : Hex.Interval.Executable.Error)
  | mismatch
  deriving DecidableEq, Repr

private def sameRegistrations (left right : Array Registration) : Bool := Id.run do
  if left.size != right.size then return false
  for index in [0:left.size] do
    let some a := left[index]? | return false
    let some b := right[index]? | return false
    if !a.same b then return false
  return true

private def proofKey (rule : RuleKey) (schema : Nat) : Proof.Key :=
  { rule, role := .fact, bodySchema := schema }

private def routeFormats? (assembly : RawAssembly Fact Cause) (rule : RuleId) :
    Option (RuleKey × Array Hex.Interval.Executable.ReplayFormat) :=
  assembly.registry.formats? rule

private def formatCoverage
    (assembly : RawAssembly Fact Cause) (proof : Proof.Registry semantics Plan) : Bool := Id.run do
  for ruleIndex in [0:assembly.registry.registrations.size] do
    let some (rule, formats) := routeFormats? assembly { index := ruleIndex } | return false
    for format in formats do
      if format.role != .fact then return false
      let key := proofKey rule format.schema
      if (proof.fact? key).isNone then return false
  for schema in proof.facts do
    let some (ruleId, _) := Registration.find? assembly.registry.registrations schema.key.rule
      | return false
    let some (_, formats) := routeFormats? assembly ruleId | return false
    if !(formats.any fun format =>
        format.role == .fact && format.schema == schema.key.bodySchema) then return false
  return proof.equalities.isEmpty && proof.instances.isEmpty &&
    proof.refuters.isEmpty && proof.splits.isEmpty

private def commonMatcherEpoch? (applications : Array Hex.Interval.Executable.Application) :
    Option Nat := Id.run do
  let mut epoch := none
  for application in applications do
    match application.matcherEpoch, epoch with
    | none, _ => pure ()
    | some current, none => epoch := some current
    | some current, some expected => if current != expected then return none
  return some (epoch.getD 0)

/-- Seal exact bidirectional fact-format coverage between one executable
assembly and one theorem registry. Equality, instance, refutation, and split
schemas are intentionally rejected at this fact-only boundary. -/
opaque Registry.buildWithin (stateLimits : State.Limits) (key : Controller.Key)
    (assembly : RawAssembly Fact Cause) (domain : FactDomain Fact)
    (proof : Proof.Registry semantics Plan) :
    Except Error (Registry Fact semantics Cause Plan) := do
  if stateLimits.maxApplications < assembly.applications.size then
    throw (.resource .applications)
  if stateLimits.maxRules < assembly.registry.registrations.size ||
      stateLimits.maxRules < proof.registrations.size then
    throw (.resource (.state .rules))
  let some formatCount := assembly.registry.formatCount? | throw .invalidRegistry
  if stateLimits.maxReplayFormats < formatCount then
    throw (.resource (.state .replayFormats))
  if !assembly.program.check ||
      !Registration.check assembly.program proof.registrations ||
      !sameRegistrations assembly.registry.registrations proof.registrations ||
      !formatCoverage assembly proof then
    throw .invalidRegistry
  let some matcherEpoch := commonMatcherEpoch? assembly.applications
    | throw .invalidRegistry
  let generations := assembly.applications.map (·.generation)
  if stateLimits.maxGeneration < matcherEpoch ||
      generations.any (fun generation => stateLimits.maxGeneration < generation) then
    throw (.resource (.state .generation))
  pure { key, assembly, domain, proof, applicationGenerations := generations, matcherEpoch }

private def branchView (branch : State.Branch Fact Cause) : ProgramView :=
  { programVersion := branch.programVersion,
    operations := branch.program.operations, nodes := branch.program.nodes,
    generations := branch.generations, depths := branch.depths }

private def request? (assembly : RawAssembly Fact Cause) (snapshot : Snapshot Fact)
    (program : ProgramView) (serial : Nat)
    (applicationId : ApplicationId) : Option (RuleRequest Fact) := do
  let application ← assembly.applications[applicationId.index]?
  let registration ← assembly.registry.registrations[application.rule.index]?
  let inputs ← application.watches.mapM fun node => do
    let fact ← snapshot.fact? node
    let version ← snapshot.version? node
    pure { node, fact, version }
  let action : Action :=
    { serial, programVersion := program.programVersion, application := applicationId,
      rule := application.rule, key := registration.key, node := application.node,
      kind := application.kind, effort := application.effort,
      generation := application.generation, inputs := inputs.map fun input =>
        { node := input.node, version := input.version },
      writes := application.writes, structuralInputs := application.structuralInputs,
      matcherEpoch := application.matcherEpoch }
  pure
    { action, program, inputs, writes := application.writes }

private def generate [DecidableEq Fact] [DecidableEq Cause]
    (envelope : Search.Envelope) (registry : Registry Fact semantics Cause Plan)
    (assembly : RawAssembly Fact Cause) (branch : State.Branch Fact Cause)
    (serial : Nat) : Except Error (Array (Search.Offer ApplicationId RuleKey)) := do
  match preflightBranch envelope.state branch with
  | .error (.resource resource) => throw (.resource resource)
  | .error _ => throw .mismatch
  | .ok _ => pure ()
  let some snapshot := branch.checkedSnapshot? | throw .mismatch
  if branch.program != assembly.program ||
      assembly.program != registry.assembly.program ||
      assembly.bindings != registry.assembly.bindings ||
      !sameRegistrations assembly.registry.registrations
        registry.assembly.registry.registrations ||
      assembly.applications.size != registry.applicationGenerations.size then
    throw .mismatch
  if envelope.state.maxApplications < assembly.applications.size then
    throw (.resource .applications)
  let program := branchView branch
  let some context := assembly.offerContext? snapshot program | throw .mismatch
  let mut offers := #[]
  for index in [0:assembly.applications.size] do
    let id : ApplicationId := { index }
    let some request := request? assembly snapshot program serial id
      | throw (.invalidApplication id)
    if registry.applicationGenerations[index]? != some request.action.generation then
      throw (.invalidApplication id)
    if context.offers request then
      if envelope.policy.maxOffers ≤ offers.size then
        throw (.search (.policy .offerLimit))
      offers := offers.push
        { view :=
            { id, key := request.action.key, offerClass := offerClass request.action.kind,
              age := serial, score := 0 }
          action := request.action }
  pure offers

private def startSession [DecidableEq Fact] [DecidableEq Cause]
    (envelope : Search.Envelope) (measure : Policy.Measure ApplicationId RuleKey)
    (registry : Registry Fact semantics Cause Plan) (assembly : RawAssembly Fact Cause)
    (scope : Policy.ScopeId) (branch : State.Branch Fact Cause) := do
  let offers ← generate envelope registry assembly branch 0
  Search.Session.startWithin envelope measure branch assembly.registry.registrations
    assembly.bindings registry.applicationGenerations #[] registry.matcherEpoch scope offers
    |>.mapError Error.search

private def refresh [DecidableEq Fact] [DecidableEq Cause]
    (envelope : Search.Envelope) (measure : Policy.Measure ApplicationId RuleKey)
    (registry : Registry Fact semantics Cause Plan) (assembly : RawAssembly Fact Cause)
    (session : Search.Session Fact Cause ApplicationId RuleKey)
    (dismissedIncomplete : Bool) := do
  let offers ← generate envelope registry assembly session.branch session.serial
  -- `Search` does not decrement `remaining`: it is a controller-owned budget
  -- view supplied at session start/refresh. As in the sibling explicit-package
  -- controller, this adapter deliberately carries the stored value unchanged.
  Search.Session.refreshWithin envelope measure session offers session.remaining dismissedIncomplete
    |>.mapError Error.search

/-- Sticky executable handle paired with the sealed controller lineage. The
assembly stored here, including its private package caches, is authoritative;
passing another same-key registry never transplants its cache value. -/
structure State (Fact Cause Plan : Type) where
  private mk ::
  compatibility : Controller.Key
  assembly : RawAssembly Fact Cause
  bundle : Driver.Bundle Fact Cause Plan
  session : Search.Session Fact Cause ApplicationId RuleKey
  choices : Nat
  dismissedIncomplete : Bool

/-- Fixed structural measure for executable offers. Application identifiers
cost one pair/cell through `Controller.policyMeasure`; rule keys additionally
charge their name bytes and schema. Only policy-state measurement is supplied
by the caller of `runWithin`. -/
def policyMeasure : Policy.Measure ApplicationId RuleKey :=
  Controller.policyMeasure fun key =>
    { bytes := key.name.length + key.schema + 1, pairs := 1, work := 1 }

opaque State.startWithin [DecidableEq Fact] [DecidableEq Cause]
    (envelope : Search.Envelope) (registry : Registry Fact semantics Cause Plan)
    (bundle : Driver.Bundle Fact Cause Plan) : Except Error (State Fact Cause Plan) :=
  match Search.Result.current? bundle.tree with
  | none => .error .mismatch
  | some (_, source) =>
      match startSession envelope policyMeasure registry registry.assembly
          source.scope source.branch with
      | .error error => .error error
      | .ok session => .ok
          { compatibility := registry.key, assembly := registry.assembly, bundle, session,
            choices := 0, dismissedIncomplete := false }

private def checkPolicy (limit : Controller.PolicyLimit)
    (measure : PolicyState → Policy.Cost) (state : PolicyState) : Except Error Unit := do
  let cost := measure state
  if limit.bytes < cost.bytes || limit.pairs < cost.pairs || limit.work < cost.work then
    throw (.resource .policyState)

private def liftExcept.{u, v} {ε : Type u} {α : Type v} (result : Except ε α) :
    Except ε (ULift α) :=
  match result with
  | .error error => .error error
  | .ok value => .ok (ULift.up value)

private def makeCommand (program : Program) (domain : FactDomain Fact)
    (proof : Proof.Registry semantics Plan)
    (request : Search.Request Fact ApplicationId RuleKey)
    (invocation : Hex.Interval.Executable.Invocation (FactOutcome Fact Cause)) :
    Except Error (Driver.Command Fact Cause ApplicationId RuleKey Plan) := do
  if invocation.rule != request.action.key ||
      invocation.quotes.size != invocation.result.proposals.size then
    throw .invalidQuote
  let mut updates := #[]
  let mut events := []
  let mut facts := request.facts.facts
  let mut versions := request.facts.versions
  let mut contradiction := false
  for index in [0:invocation.result.proposals.size] do
    let some proposal := invocation.result.proposals[index]? | throw .invalidQuote
    let some quote := invocation.quotes[index]? | throw .invalidQuote
    if quote.role != .fact then throw .invalidQuote
    let key := proofKey invocation.rule quote.schema
    let some schema := proof.fact? key | throw (.missingSchema key)
    if (schema.decode quote.body).isNone then throw (.invalidBody key)
    if !request.action.writes.contains proposal.node then throw .mismatch
    let some instruction := program.node? proposal.node | throw .mismatch
    let some previous := facts[proposal.node.index]? | throw .mismatch
    let some version := versions[proposal.node.index]? | throw .mismatch
    let (installed, refuted) ← match domain.narrow instruction.domain previous proposal.proposed with
      | .improved fact => pure (fact, false)
      | .contradiction fact => pure (fact, true)
      | .resourceLimit budget => throw (.resource (.narrow budget))
      | _ => throw .mismatch
    let update : State.Update Fact Cause :=
      { programVersion := request.programVersion, node := proposal.node,
        previous := { node := proposal.node, version }, fact := installed,
        version := version + 1, cause := proposal.cause }
    updates := updates.push update
    facts := facts.set! proposal.node.index installed
    versions := versions.set! proposal.node.index (version + 1)
    contradiction := contradiction || refuted
    events := events ++ [.fact
      { scope := request.scope, programVersion := request.programVersion,
        action := request.action, node := proposal.node,
        previous := update.previous, version := update.version,
        proposed := proposal.proposed, installed,
        assumptions := request.action.inputs, schema := key, body := quote.body }]
  let outcome : Search.Outcome Fact Cause ApplicationId RuleKey :=
    { scope := request.scope, serial := request.serial,
      programVersion := request.programVersion, offer := request.offer,
      action := request.action, updates,
      contradiction,
      diagnostic := invocation.result.diagnostic }
  pure (.continue { outcome, events })

private def invoke [DecidableEq Fact] (limits : Hex.Interval.Executable.Limits)
    (domain : FactDomain Fact) (proof : Proof.Registry semantics Plan)
    (assembly : RawAssembly Fact Cause)
    (branch : State.Branch Fact Cause)
    (request : Search.Request Fact ApplicationId RuleKey) :
    Driver.Command Fact Cause ApplicationId RuleKey Plan ×
      Except Error (RawAssembly Fact Cause) :=
  match request? assembly branch.snapshot (branchView branch) request.serial
      request.action.application with
  | none => (.stop 0, .error (.invalidApplication request.action.application))
  | some exact =>
      let requestedFacts := request.action.inputs.mapM fun seen => request.facts.fact? seen.node
      if exact.action != request.action then
        (.stop 0, .error .mismatch)
      else match requestedFacts with
        | none => (.stop 0, .error .mismatch)
        | some facts =>
          if _ : facts = exact.inputs.map fun input => input.fact then
            match assembly.invokeWithin limits exact with
            | .error error => (.stop 0, .error (.executable error))
            | .ok (invocation, next) =>
                match makeCommand assembly.program domain proof request invocation with
                | .error error => (.stop 0, .error error)
                | .ok command => (command, .ok next)
          else (.stop 0, .error .mismatch)

/-- The current fact-only adapter exposes resumable policy/callback stops only.
It has no typed target, refutation, split, or unknown correlation, so such
Driver outcomes are rejected as `mismatch`; those terminal interfaces require
their own executable quotation/schema adapters. -/
inductive Run (Fact Cause Plan PolicyState : Type)
  | stopped (stop : Search.Stop Unit Unit) (state : State Fact Cause Plan)
      (policy : PolicyState)

/-- Run the fact-only executable adapter until the policy stops or a resource
cap is exhausted. Every accepted invocation updates the sticky assembly cache,
then regenerates offers from that exact replacement assembly. -/
opaque runWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq Plan]
    (limits : Controller.Limits) (executableLimits : Hex.Interval.Executable.Limits)
    (envelope : Search.Envelope) (policyStateMeasure : PolicyState → Policy.Cost)
    (resultMeasure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (recipeMeasure : Driver.Measure Fact)
    (registry : Registry Fact semantics Cause Plan)
    (policy : Policy.Interface Fact PolicyState ApplicationId RuleKey)
    (policyState : PolicyState) (initial : State Fact Cause Plan) :
    Except Error (Run Fact Cause Plan PolicyState) := do
  if initial.compatibility != registry.key then throw .mismatch
  let _ ← liftExcept (checkPolicy limits.policyState policyStateMeasure policyState)
  let rec loop (fuel : Nat) (state : State Fact Cause Plan) (policyState : PolicyState) := do
    if state.choices >= limits.maxChoices then throw (.resource .choices)
    match fuel with
    | 0 => throw (.resource .choices)
    | fuel + 1 =>
      let choice := (← liftExcept (Search.chooseWithin envelope policyMeasure policy policyState
        state.session |>.mapError Error.search)).down
      match choice with
      | .stopped stop next =>
          let _ ← liftExcept (checkPolicy limits.policyState policyStateMeasure next)
          pure (.stopped stop state next)
      | .dismiss decision next =>
          let _ ← liftExcept (checkPolicy limits.policyState policyStateMeasure next)
          let offers := state.session.offers.filter fun offer => offer.view.id != decision.id
          if offers.size + 1 != state.session.offers.size then throw .mismatch
          let dismissedIncomplete := state.dismissedIncomplete || decision.offerClass != .split
          let session := (← liftExcept (Search.Session.refreshWithin envelope policyMeasure
            state.session offers state.session.remaining dismissedIncomplete
              |>.mapError Error.search)).down
          loop fuel { state with session, choices := state.choices + 1, dismissedIncomplete } next
      | .select decision next =>
          let _ ← liftExcept (checkPolicy limits.policyState policyStateMeasure next)
          let callback : Search.Request Fact ApplicationId RuleKey →
              Driver.Command Fact Cause ApplicationId RuleKey Plan ×
                Except Error (RawAssembly Fact Cause) :=
            invoke executableLimits registry.domain registry.proof state.assembly state.session.branch
          let produced : Driver.Produced Fact Cause ApplicationId RuleKey Plan
              (Except Error (RawAssembly Fact Cause)) ←
            Driver.runWithWithin envelope policyMeasure limits.driver resultMeasure
            recipeMeasure .depthFirst decision.expected callback
            state.bundle state.session decision |>.mapError Error.driver
          let choices := state.choices + 1
          match produced.payload with
          | none => match produced.step with
            | .stopped stop bundle session => pure (.stopped stop
                { state with bundle, session, choices } next)
            | _ => throw .mismatch
          | some (.error error) => throw error
          | some (.ok assembly) => match produced.step with
            | .continued bundle session =>
                let session := (← liftExcept (refresh envelope policyMeasure registry assembly
                  session state.dismissedIncomplete)).down
                loop fuel
                  { compatibility := state.compatibility, assembly, bundle, session, choices,
                    dismissedIncomplete := state.dismissedIncomplete } next
            | _ => throw .mismatch
  loop limits.maxChoices initial policyState

end Executable

end Hex.Interval.Controller
