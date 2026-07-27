/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Propagator

@[expose] public section

/-!
# Engine-owned policy offers for arbitrary interval propagators

This experiment puts a replaceable search policy in front of the generic
propagator engine.  The policy sees bounded, semantic descriptions of live
work.  It can echo one description back, but it cannot construct an action,
change a fact, activate an equality, instantiate an expression, or prepare a
split.  Those transitions remain engine-owned and are revalidated at the
point of selection.

The existing append-only FIFO queue remains available as a reference
scheduler.  This layer deliberately derives a dense live frontier from the
engine's dirty bits, so scan and event-indexed policy representations can be
compared before either becomes the production representation.
-/

namespace Hex.Interval.Experiment.Propagator.Policy

/-! ## Stable semantic offer descriptions -/

/-- Scope identity is explicit even though the first experiment has one root
scope.  It prevents a later branch-local choice from being transplanted. -/
structure ScopeId where
  index : Nat
  deriving DecidableEq, Repr

/-- Versioned name of a deterministic external policy. -/
structure PolicyKey where
  name : String
  version : Nat
  deriving DecidableEq, Repr

/-- Collision-free engine identity for each kind of live work. -/
inductive OfferId where
  | application (application : ApplicationId)
  | equality (equality : EqualityId)
  | suggestion (suggestion : SuggestionId)
  deriving DecidableEq, Repr

/-- Complete payload-free identity of one concrete propagator invocation. -/
structure InvocationKey where
  scope : ScopeId
  programVersion : Nat
  application : ApplicationId
  rule : RuleKey
  anchor : NodeId
  kind : ActionKind
  effort : Nat
  inputs : List SeenVersion
  deriving DecidableEq, Repr

/-- Complete identity of an equality contraction against two fact versions. -/
structure EqualityWorkKey where
  scope : ScopeId
  programVersion : Nat
  equality : EqualityId
  left : SeenVersion
  right : SeenVersion
  deriving DecidableEq, Repr

/-- Payload-erased proposed node.  Proposal order is retained in this first
experiment; canonicalization alternatives are compared in conformance data. -/
structure ProposedNodeKey where
  domain : DomainId
  op : OpId
  args : List NodeRef
  deriving DecidableEq, Repr

/-- Payload-erased proposed equality. -/
structure ProposedEqualityKey where
  left : NodeRef
  right : NodeRef
  deriving DecidableEq, Repr

/-- Payload-erased structural identity of an instantiation request. -/
structure InstantiationSemanticKey where
  family : Nat
  triggers : List NodeId
  claimedGeneration : Nat
  nodes : List ProposedNodeKey
  equalities : List ProposedEqualityKey
  deriving DecidableEq, Repr

def InstantiationSemanticKey.ofRequest
    (request : InstantiationRequest) : InstantiationSemanticKey :=
  { family := request.key
    triggers := request.triggers
    claimedGeneration := request.claimedGeneration
    nodes := request.nodes.map fun node =>
      { domain := node.domain, op := node.op, args := node.args }
    equalities := request.equalities.map fun equality =>
      { left := equality.left, right := equality.right } }

inductive OfferClass where
  | invoke
  | equality
  | retry
  | instantiate
  | split
  deriving DecidableEq, Repr

/-- Semantic key which a selection must echo exactly.  Split freshness
includes the target fact version, not an unrelated whole-program version. -/
inductive OfferKey where
  | invoke (invocation : InvocationKey)
  | equality (contractor : EqualityWorkKey)
  | retry (source : InvocationKey) (effort : Nat)
  | instantiate (source : InvocationKey) (request : InstantiationSemanticKey)
  | split (source : InvocationKey) (target : SeenVersion) (point : Dyadic)
      (reason : SplitReason)
  deriving DecidableEq

def OfferKey.offerClass : OfferKey -> OfferClass
  | .invoke _ => .invoke
  | .equality _ => .equality
  | .retry _ _ => .retry
  | .instantiate _ _ => .instantiate
  | .split _ _ _ _ => .split

structure PolicyFeature where
  key : Nat
  value : Int
  deriving DecidableEq, Repr

structure ObservationSummary where
  outcome : Nat
  changedFacts : Nat
  logicalWork : Nat
  deriving DecidableEq, Repr

structure OfferView where
  id : OfferId
  key : OfferKey
  offerClass : OfferClass
  age : Nat
  summary : Option ObservationSummary := none
  features : Array PolicyFeature := #[]

/-! ## Engine-owned frontier state -/

/-- Policy resources are independent of proof-producing engine resources. -/
structure Limits where
  maxDecisions : Nat
  maxTraversal : Nat
  maxLiveOffers : Nat
  deriving DecidableEq, Repr

structure Clock where
  active : Bool
  born : Nat
  deriving DecidableEq, Repr

/-- A retained suggestion needs one additional guard that is not present in
its source action: the target version against which a split was proposed. -/
structure SuggestionClock where
  active : Bool
  born : Nat
  splitVersion : Option Nat
  deriving DecidableEq, Repr

structure Metrics where
  decisions : Nat := 0
  rejected : Nat := 0
  traversal : Nat := 0
  selectedInvocations : Nat := 0
  selectedEqualities : Nat := 0
  selectedRetries : Nat := 0
  selectedInstances : Nat := 0
  selectedSplits : Nat := 0
  dismissals : Nat := 0
  deriving DecidableEq, Repr

/-- Trusted frontier bookkeeping around the generic propagator engine.
Arbitrary policy-private state lives outside this structure. -/
structure State (Fact : Type) where
  scope : ScopeId
  serial : Nat
  epoch : Nat
  engine : Engine Fact
  applications : Array Clock
  equalities : Array Clock
  suggestions : Array SuggestionClock
  incomplete : Bool := false
  metrics : Metrics := {}
  limits : Limits

def clockArray (bits : Array Bool) (born : Nat) : Array Clock :=
  bits.map fun active => { active, born }

def splitVersion? (engine : Engine Fact) (suggestion : RetainedSuggestion) : Option Nat :=
  match suggestion.suggestion with
  | .split request => engine.versions[request.node.index]?
  | .retry _ | .instantiate _ => none

def suggestionClocksFrom (engine : Engine Fact) (born : Nat) : Array SuggestionClock :=
  engine.suggestions.map fun retained =>
    { active := true, born, splitVersion := splitVersion? engine retained }

/-- Begin policy control over an existing engine snapshot. -/
def State.start (engine : Engine Fact) (limits : Limits)
    (scope : ScopeId := { index := 0 }) : State Fact :=
  { scope
    serial := 0
    epoch := 0
    engine
    applications := clockArray engine.queued 0
    equalities := clockArray engine.equalityQueued 0
    suggestions := suggestionClocksFrom engine 0
    limits }

def syncClocks (epoch : Nat) (old : Array Clock) (bits : Array Bool) : Array Clock := Id.run do
  let mut clocks := #[]
  for index in [0:bits.size] do
    let active := bits[index]!
    let clock := match old[index]? with
      | some previous =>
          if active then
            if previous.active then previous else { active := true, born := epoch }
          else
            { previous with active := false }
      | none => { active, born := epoch }
    clocks := clocks.push clock
  return clocks

def syncSuggestionClocks (epoch : Nat) (engine : Engine Fact)
    (old : Array SuggestionClock) : Array SuggestionClock := Id.run do
  let mut clocks := #[]
  for index in [0:engine.suggestions.size] do
    let clock := match old[index]? with
      | some previous => previous
      | none =>
          match engine.suggestions[index]? with
          | some retained =>
              { active := true
                born := epoch
                splitVersion := splitVersion? engine retained }
          | none => { active := false, born := epoch, splitVersion := none }
    clocks := clocks.push clock
  return clocks

def invocationOfAction (scope : ScopeId) (action : Action) : InvocationKey :=
  { scope
    programVersion := action.programVersion
    application := action.application
    rule := action.key
    anchor := action.node
    kind := action.kind
    effort := action.effort
    inputs := action.inputs }

def State.invocationKey? (state : State Fact) (applicationId : ApplicationId)
    (effort : Option Nat := none) : Option InvocationKey := do
  let application <- state.engine.applications[applicationId.index]?
  let rule <- state.engine.rules[application.rule.index]?
  let inputs <- state.engine.seenVersions? application.watches
  some
    { scope := state.scope
      programVersion := state.engine.programVersion
      application := applicationId
      rule := rule.key
      anchor := application.node
      kind := application.kind
      effort := effort.getD application.effort
      inputs }

def State.equalityKey? (state : State Fact) (equalityId : EqualityId) : Option EqualityWorkKey := do
  let equality <- state.engine.equalities[equalityId.index]?
  let leftVersion <- state.engine.versions[equality.left.index]?
  let rightVersion <- state.engine.versions[equality.right.index]?
  some
    { scope := state.scope
      programVersion := state.engine.programVersion
      equality := equalityId
      left := { node := equality.left, version := leftVersion }
      right := { node := equality.right, version := rightVersion } }

def actionFresh (state : State Fact) (action : Action) : Bool :=
  match state.engine.applications[action.application.index]?,
      state.engine.rules[action.rule.index]?,
      state.engine.seenVersions? (action.inputs.map fun input => input.node) with
  | some application, some rule, some current =>
      application.rule == action.rule && application.node == action.node &&
        application.kind == action.kind && rule.key == action.key &&
        action.inputs.map (fun input => input.node) == application.watches &&
        current == action.inputs
  | _, _, _ => false

def State.suggestionKey? (state : State Fact) (suggestionId : SuggestionId) : Option OfferKey := do
  let clock <- state.suggestions[suggestionId.index]?
  if !clock.active then none else pure ()
  let retained <- state.engine.suggestions[suggestionId.index]?
  if !actionFresh state retained.action then none else pure ()
  let source := invocationOfAction state.scope retained.action
  match retained.suggestion with
  | .retry effort =>
      if retained.action.effort < effort && effort <= state.engine.limits.maxEffort then
        some (.retry source effort)
      else none
  | .instantiate request =>
      if retained.action.programVersion == state.engine.programVersion then
        some (.instantiate source (.ofRequest request))
      else none
  | .split request => do
      let version <- clock.splitVersion
      let current <- state.engine.versions[request.node.index]?
      if current != version then none else pure ()
      if !(EndpointCost.ofDyadic request.point).allowed
          state.engine.limits.splitEndpointLimit then none else pure ()
      some (.split source { node := request.node, version } request.point request.reason)

/-- Permanently tombstone suggestions whose freshness guard has failed. -/
def State.pruneSuggestions (state : State Fact) : State Fact := Id.run do
  let mut clocks := state.suggestions
  for index in [0:clocks.size] do
    match clocks[index]? with
    | some clock =>
        if clock.active && (state.suggestionKey? { index }).isNone then
          clocks := clocks.set! index { clock with active := false }
    | none => pure ()
  return { state with suggestions := clocks }

/-- Install a new engine snapshot, refresh live work clocks, and tombstone
stale suggestions.  Previously consumed suggestions never reactivate. -/
def State.advance (state : State Fact) (engine : Engine Fact) : State Fact :=
  let epoch := state.epoch + 1
  let next : State Fact :=
    { state with
      epoch
      engine
      applications := syncClocks epoch state.applications engine.queued
      equalities := syncClocks epoch state.equalities engine.equalityQueued
      suggestions := syncSuggestionClocks epoch engine state.suggestions }
  next.pruneSuggestions

def State.offer? (state : State Fact) : OfferId -> Option OfferView
  | .application application => do
      let clock <- state.applications[application.index]?
      if !clock.active || state.engine.pending.isSome || state.engine.contradictory then none
      else pure ()
      let queued <- state.engine.queued[application.index]?
      if !queued then none else pure ()
      let key <- state.invocationKey? application
      some
        { id := .application application
          key := .invoke key
          offerClass := .invoke
          age := state.epoch - clock.born }
  | .equality equality => do
      let clock <- state.equalities[equality.index]?
      if !clock.active || state.engine.pending.isSome || state.engine.contradictory then none
      else pure ()
      let queued <- state.engine.equalityQueued[equality.index]?
      if !queued then none else pure ()
      let key <- state.equalityKey? equality
      some
        { id := .equality equality
          key := .equality key
          offerClass := .equality
          age := state.epoch - clock.born }
  | .suggestion suggestion => do
      if state.engine.pending.isSome || state.engine.contradictory then none else pure ()
      let clock <- state.suggestions[suggestion.index]?
      let key <- state.suggestionKey? suggestion
      some
        { id := .suggestion suggestion
          key
          offerClass := key.offerClass
          age := state.epoch - clock.born }

inductive ViewError where
  | malformedState
  | decisionLimit
  | traversalLimit
  | liveOfferLimit
  deriving DecidableEq, Repr

/-- Authoritative bounded scan of every live semantic offer. -/
def State.offers (state : State Fact) : Except ViewError (Array OfferView × Nat) := do
  let traversal := state.applications.size + state.equalities.size + state.suggestions.size
  if state.limits.maxTraversal < state.metrics.traversal + traversal then
    throw .traversalLimit
  let mut offers := #[]
  for index in [0:state.applications.size] do
    if let some offer := state.offer? (.application { index }) then
      offers := offers.push offer
  for index in [0:state.equalities.size] do
    if let some offer := state.offer? (.equality { index }) then
      offers := offers.push offer
  for index in [0:state.suggestions.size] do
    if let some offer := state.offer? (.suggestion { index }) then
      offers := offers.push offer
  if state.limits.maxLiveOffers < offers.size then throw .liveOfferLimit
  pure (offers, traversal)

structure EngineBudgetView where
  actions : Nat
  acceptedFacts : Nat
  nodes : Nat
  equalities : Nat
  deriving DecidableEq, Repr

structure View (Fact : Type) where
  scope : ScopeId
  serial : Nat
  programVersion : Nat
  offers : Array OfferView
  facts : Snapshot Fact
  remaining : EngineBudgetView

def remaining (limit used : Nat) : Nat := limit - used

def State.view (state : State Fact) : Except ViewError (View Fact × State Fact) := do
  if state.limits.maxDecisions <= state.metrics.decisions then throw .decisionLimit
  let (offers, traversal) <- state.offers
  pure
    ({ scope := state.scope
       serial := state.serial
       programVersion := state.engine.programVersion
       offers
       facts := state.engine.snapshot
       remaining :=
        { actions := remaining state.engine.limits.maxActions state.engine.metrics.queuePops
          acceptedFacts := remaining state.engine.limits.maxAcceptedFacts state.engine.history.size
          nodes := remaining state.engine.limits.maxNodes state.engine.program.nodes.size
          equalities := remaining state.engine.limits.maxEqualities state.engine.equalities.size } },
     { state with
       metrics := { state.metrics with traversal := state.metrics.traversal + traversal } })

/-! ## Validated selection -/

/-- A policy echoes both the engine identity and the semantic key from one
particular view. -/
structure Selection where
  scope : ScopeId
  serial : Nat
  programVersion : Nat
  id : OfferId
  expected : OfferKey

inductive Rejection where
  | decisionLimit
  | wrongScope
  | staleSerial
  | staleProgram
  | missingOffer
  | wrongKey
  | actionLimit
  | malformedState
  deriving DecidableEq, Repr

structure FactDelta (Fact : Type) where
  node : NodeId
  before : Fact
  after : Fact
  beforeVersion : Nat
  afterVersion : Nat

inductive EqualityOutcome where
  | noChange
  | improved
  | contradiction
  | engineResource (resource : Resource)
  | factResource (budget : Nat)
  | invalid (code : Nat)
  deriving DecidableEq, Repr

/-- Equality work gets the same typed observation treatment as external rule
work; otherwise a policy could not learn from every selectable transition. -/
structure EqualityObservation (Fact : Type) where
  key : EqualityWorkKey
  outcome : EqualityOutcome
  changes : Array (FactDelta Fact)
  narrowCalls : Nat

structure SplitPlan (Fact : Type) where
  scope : ScopeId
  suggestion : SuggestionId
  origin : Action
  node : NodeId
  version : Nat
  fact : Fact
  point : Dyadic
  reason : SplitReason
  source : InvocationKey

inductive Completed where
  | instanceAdmitted (newNodes : List NodeId)
  | instanceDuplicate
  | instanceRejected (error : AdmissionError)
  | dismissed
  deriving Repr

inductive SelectResult (Fact : Type) where
  | request (request : RuleRequest Fact) (state : State Fact)
  | equality (observation : EqualityObservation Fact) (state : State Fact)
  | completed (completion : Completed) (state : State Fact)
  | split (plan : SplitPlan Fact) (state : State Fact)
  | rejected (reason : Rejection) (state : State Fact)
  | engineResource (resource : Resource) (state : State Fact)
  | factResource (budget : Nat) (state : State Fact)

def State.chargeDecision (state : State Fact) (rejected : Bool := false) : State Fact :=
  { state with
    serial := state.serial + 1
    metrics :=
      { state.metrics with
        decisions := state.metrics.decisions + 1
        rejected := state.metrics.rejected + if rejected then 1 else 0 } }

def State.reject (state : State Fact) (reason : Rejection) : SelectResult Fact :=
  match reason with
  | .decisionLimit => .rejected reason state
  | _ => .rejected reason (state.chargeDecision true)

def State.validate (state : State Fact) (selection : Selection) : Except Rejection OfferView := do
  if state.limits.maxDecisions <= state.metrics.decisions then throw .decisionLimit
  if selection.scope != state.scope then throw .wrongScope
  if selection.serial != state.serial then throw .staleSerial
  if selection.programVersion != state.engine.programVersion then throw .staleProgram
  let some offer := state.offer? selection.id | throw .missingOffer
  if selection.expected != offer.key then throw .wrongKey
  pure offer

def deltasFor (before after : Engine Fact) (nodes : List NodeId) : Array (FactDelta Fact) := Id.run do
  let mut deltas := #[]
  for node in dedupList nodes do
    match before.facts[node.index]?, after.facts[node.index]?,
        before.versions[node.index]?, after.versions[node.index]? with
    | some beforeFact, some afterFact, some beforeVersion, some afterVersion =>
        if beforeVersion != afterVersion then
          deltas := deltas.push
            { node, before := beforeFact, after := afterFact, beforeVersion, afterVersion }
    | _, _, _, _ => pure ()
  return deltas

/-- Freeze an application only after validating the selected semantic offer.
The optional effort is supplied only by an engine-retained retry offer. -/
def State.prepareApplication (state : State Fact) (applicationId : ApplicationId)
    (effort : Option Nat) (clearDirty : Bool) : SelectResult Fact :=
  if state.engine.limits.maxActions <= state.engine.metrics.queuePops then
    .rejected .actionLimit (state.chargeDecision true)
  else
    match state.engine.applications[applicationId.index]? with
    | none => state.reject .malformedState
    | some application =>
        match state.engine.rules[application.rule.index]?,
            state.engine.seenVersions? application.watches,
            state.engine.factViews? application.watches with
        | some rule, some inputs, some views =>
            let action : Action :=
              { serial := state.engine.metrics.requests
                programVersion := state.engine.programVersion
                application := applicationId
                rule := application.rule
                key := rule.key
                node := application.node
                kind := application.kind
                effort := effort.getD application.effort
                inputs }
            let queued :=
              if clearDirty then state.engine.queued.set! applicationId.index false
              else state.engine.queued
            let engine : Engine Fact :=
              { state.engine with
                queued
                pending := some action
                metrics :=
                  { state.engine.metrics with
                    queuePops := state.engine.metrics.queuePops + 1
                    requests := state.engine.metrics.requests + 1 } }
            let state := (state.advance engine).chargeDecision
            .request { action, inputs := views, writes := application.writes } state
        | _, _, _ => state.reject .malformedState

def State.consumeSuggestion (state : State Fact) (suggestion : SuggestionId) : State Fact :=
  match state.suggestions[suggestion.index]? with
  | none => state
  | some clock =>
      { state with
        suggestions := state.suggestions.set! suggestion.index { clock with active := false } }

def equalityObservation (key : EqualityWorkKey) (before after : Engine Fact)
    (outcome : EqualityOutcome) (narrowCalls : Nat) : EqualityObservation Fact :=
  { key
    outcome
    changes := deltasFor before after [key.left.node, key.right.node]
    narrowCalls }

def State.selectEquality (state : State Fact) (key : EqualityWorkKey) : SelectResult Fact :=
  if state.engine.limits.maxActions <= state.engine.metrics.queuePops then
    .rejected .actionLimit (state.chargeDecision true)
  else
    let running : Engine Fact :=
      { state.engine with
        equalityQueued := state.engine.equalityQueued.set! key.equality.index false
        metrics :=
          { state.engine.metrics with
            queuePops := state.engine.metrics.queuePops + 1
            equalityRuns := state.engine.metrics.equalityRuns + 1 } }
    let selected :=
      match state.equalities[key.equality.index]? with
      | some clock =>
          { state with
            engine := running
            equalities := state.equalities.set! key.equality.index { clock with active := false } }
      | none => { state with engine := running }
    match running.contractEquality key.equality with
    | .advanced engine =>
        let outcome :=
          if engine.contradictory && !state.engine.contradictory then .contradiction
          else if engine.history.size == state.engine.history.size then .noChange
          else .improved
        let observation := equalityObservation key state.engine engine outcome 2
        let next := selected.advance engine
        .equality observation
          { (next.chargeDecision) with
            metrics :=
              { next.metrics with
                decisions := next.metrics.decisions + 1
                selectedEqualities := next.metrics.selectedEqualities + 1 } }
    | .invalid code engine =>
        .equality (equalityObservation key state.engine engine (.invalid code) 0)
          ((selected.advance engine).chargeDecision)
    | .resourceLimit resource engine =>
        .engineResource resource ((selected.advance engine).chargeDecision)
    | .factResourceLimit budget engine =>
        .factResource budget ((selected.advance engine).chargeDecision)

def State.selectSuggestion (state : State Fact) (suggestionId : SuggestionId)
    (key : OfferKey) : SelectResult Fact :=
  let consumed := state.consumeSuggestion suggestionId
  match state.engine.suggestions[suggestionId.index]? with
  | none => state.reject .malformedState
  | some retained =>
      match key, retained.suggestion with
      | .retry _ effort, .retry retainedEffort =>
          if effort != retainedEffort then state.reject .wrongKey
          else
            match consumed.prepareApplication retained.action.application (some effort) false with
            | .request request next =>
                .request request
                  { next with
                    metrics :=
                      { next.metrics with selectedRetries := next.metrics.selectedRetries + 1 } }
            | result => result
      | .instantiate _ _, .instantiate _ =>
          match consumed.engine.admitInstantiation suggestionId with
          | .admitted nodes engine =>
              let next := consumed.advance engine
              .completed (.instanceAdmitted nodes)
                { (next.chargeDecision) with
                  metrics :=
                    { next.metrics with
                      decisions := next.metrics.decisions + 1
                      selectedInstances := next.metrics.selectedInstances + 1 } }
          | .duplicate engine =>
              .completed .instanceDuplicate ((consumed.advance engine).chargeDecision)
          | .invalid error engine =>
              .completed (.instanceRejected error) ((consumed.advance engine).chargeDecision)
          | .resourceLimit resource engine =>
              .engineResource resource ((consumed.advance engine).chargeDecision)
      | .split source target point reason, .split request =>
          match consumed.engine.facts[target.node.index]? with
          | none => state.reject .malformedState
          | some fact =>
              let consumed := { consumed with epoch := consumed.epoch + 1 }
              .split
                { scope := state.scope
                  node := request.node
                  suggestion := suggestionId
                  origin := retained.action
                  version := target.version
                  fact
                  point
                  reason
                  source }
                { (consumed.chargeDecision) with
                  metrics :=
                    { consumed.metrics with
                      decisions := consumed.metrics.decisions + 1
                      selectedSplits := consumed.metrics.selectedSplits + 1 } }
      | _, _ => state.reject .wrongKey

/-- Recheck and execute one policy selection. -/
def State.select (state : State Fact) (selection : Selection) : SelectResult Fact :=
  match state.validate selection with
  | .error reason => state.reject reason
  | .ok offer =>
      match selection.id, offer.key with
      | .application application, .invoke _ =>
          match state.prepareApplication application none true with
          | .request request next =>
              .request request
                { next with
                  metrics :=
                    { next.metrics with
                      selectedInvocations := next.metrics.selectedInvocations + 1 } }
          | result => result
      | .equality _, .equality key => state.selectEquality key
      | .suggestion suggestion, key => state.selectSuggestion suggestion key
      | _, _ => state.reject .wrongKey

/-- Dismissing ordinary propagation work makes the run incomplete; dismissing
a suggestion merely declines one optional search action. -/
def State.dismiss (state : State Fact) (selection : Selection) : SelectResult Fact :=
  match state.validate selection with
  | .error reason => state.reject reason
  | .ok _ =>
      let next := match selection.id with
        | .application application =>
            let engine :=
              { state.engine with queued := state.engine.queued.set! application.index false }
            { state.advance engine with incomplete := true }
        | .equality equality =>
            let engine :=
              { state.engine with
                equalityQueued := state.engine.equalityQueued.set! equality.index false }
            { state.advance engine with incomplete := true }
        | .suggestion suggestion =>
            let next := state.consumeSuggestion suggestion
            { next with epoch := next.epoch + 1 }
      let next := next.chargeDecision
      .completed .dismissed
        { next with metrics := { next.metrics with dismissals := next.metrics.dismissals + 1 } }

/-! ## Exact rule observations -/

inductive OutcomeTag where
  | success
  | noChange
  | inapplicable
  | resourceLimit (budget : Nat)
  | failed (code : Nat)
  deriving DecidableEq, Repr

def outcomeTag : Outcome Fact -> OutcomeTag
  | .success _ _ _ => .success
  | .noChange _ => .noChange
  | .inapplicable => .inapplicable
  | .resourceLimit budget => .resourceLimit budget
  | .failed code => .failed code

def outcomeCost : Outcome Fact -> CostObservation
  | .success _ _ cost | .noChange cost => cost
  | .inapplicable | .resourceLimit _ | .failed _ => {}

structure RuleObservation (Fact : Type) where
  invocation : InvocationKey
  outcome : OutcomeTag
  changes : Array (FactDelta Fact)
  contradiction : Bool
  cost : CostObservation
  emittedSuggestions : Array OfferId

def emittedSuggestions (before after : Nat) : Array OfferId := Id.run do
  let mut emitted := #[]
  for offset in [0:after - before] do
    emitted := emitted.push (.suggestion { index := before + offset })
  return emitted

inductive SubmitResult (Fact : Type) where
  | accepted (observation : RuleObservation Fact) (state : State Fact)
  | invalid (error : ReplyError) (state : State Fact)
  | engineResource (resource : Resource) (state : State Fact)
  | factResource (budget : Nat) (state : State Fact)
  | malformedState (state : State Fact)

/-- Admit a reply through the underlying engine, then expose actual admitted
fact deltas and newly engine-indexed suggestions.  Claimed candidate strength
is never used as an observation. -/
def State.submit (state : State Fact) (reply : Reply Fact) : SubmitResult Fact :=
  match state.engine.pending with
  | none => .malformedState state
  | some action =>
      match state.engine.applications[action.application.index]? with
      | none => .malformedState state
      | some application =>
          let before := state.engine
          match before.submit reply with
          | .accepted engine =>
              let observation : RuleObservation Fact :=
                { invocation := invocationOfAction state.scope action
                  outcome := outcomeTag reply.outcome
                  changes := deltasFor before engine application.writes
                  contradiction := engine.contradictory && !before.contradictory
                  cost := outcomeCost reply.outcome
                  emittedSuggestions :=
                    emittedSuggestions before.suggestions.size engine.suggestions.size }
              .accepted observation (state.advance engine)
          | .invalid error engine => .invalid error (state.advance engine)
          | .resourceLimit resource engine =>
              .engineResource resource (state.advance engine)
          | .factResourceLimit budget engine => .factResource budget (state.advance engine)

end Hex.Interval.Experiment.Propagator.Policy
