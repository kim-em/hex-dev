/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.Policy

/-!
# Policy-frontier representation experiment

This experiment compares a complete frontier scan with a maintained binary
max-heap over the same engine-owned semantic offers.  Both arms run the same
non-FIFO policy and cross the same validated selection boundary.  The indexed
arm is seeded by one complete view, then consumes only newly appended engine
work and suggestion events.

The accounting deliberately includes work omitted by the first spike:

* every backing slot inspected and live offer emitted by `Policy.State.view`;
* every clock slot rebuilt when the policy wrapper advances and every retained
  suggestion revisited by pruning;
* every dependency insertion attempt, including suppressed dense wakes;
* every appended event consumed by the maintained frontier;
* every explicit semantic-offer recheck, priority comparison, and heap move.

These are deterministic logical counts, not a wall-clock cost model.  In
particular, one unit in two different columns need not have the same machine
cost.  The vector is useful for finding missing work and asymptotic regimes;
it does not by itself choose a production representation.
-/

namespace Hex.Interval.Experiment.Propagator.PolicyFrontier

open Policy

abbrev Rank := Nat

/-! # Workloads over opaque arbitrary functions -/

/-- One public-API workload.  In a dense workload every sink watches every
root; otherwise every sink watches only root zero.  Each post-trigger sink
reply also emits `churn` disposable split suggestions. -/
structure Workload where
  name : String
  roots : Nat
  sinks : Nat
  churn : Nat
  dense : Bool
  deriving DecidableEq, Repr

def Workload.valid (workload : Workload) : Bool :=
  0 < workload.roots && 0 < workload.sinks

def fanoutCanary : Workload :=
  { name := "fanout", roots := 1, sinks := 6, churn := 0, dense := false }

def denseCanary : Workload :=
  { name := "dense", roots := 4, sinks := 5, churn := 0, dense := true }

def churnCanary : Workload :=
  { name := "churn", roots := 1, sinks := 5, churn := 3, dense := false }

def rankDomainId : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "policy-frontier.source" }

def controlKey : OpKey := { name := "policy-frontier.control" }

def sinkKey : OpKey := { name := "policy-frontier.sink" }

def controlRuleKey : RuleKey := { name := "policy-frontier.control-trigger" }

def sinkRuleKey : RuleKey := { name := "policy-frontier.sink-forward" }

def nodeId (index : Nat) : NodeId := { index }

def applicationId (index : Nat) : ApplicationId := { index }

def suggestionId (index : Nat) : SuggestionId := { index }

def rootIds (workload : Workload) : List NodeId :=
  (List.range workload.roots).map nodeId

def argumentSlots (count : Nat) : List Slot :=
  (List.range count).map Slot.argument

def sinkArity (workload : Workload) : Nat :=
  if workload.dense then workload.roots else 1

def operations (workload : Workload) : Array Operation :=
  #[{ key := sourceKey, inputs := [], output := rankDomainId },
    { key := controlKey
      inputs := List.replicate workload.roots rankDomainId
      output := rankDomainId },
    { key := sinkKey
      inputs := List.replicate (sinkArity workload) rankDomainId
      output := rankDomainId }]

def program (workload : Workload) : Program := Id.run do
  let mut nodes := #[]
  for _ in [0:workload.roots] do
    nodes := nodes.push
      { domain := rankDomainId, op := { index := 0 }, args := [] }
  nodes := nodes.push
    { domain := rankDomainId
      op := { index := 1 }
      args := rootIds workload }
  let sinkArgs :=
    if workload.dense then rootIds workload else [nodeId 0]
  for _ in [0:workload.sinks] do
    nodes := nodes.push
      { domain := rankDomainId, op := { index := 2 }, args := sinkArgs }
  return { operations := operations workload, nodes }

def rules (workload : Workload) : Array Registration :=
  #[{ key := controlRuleKey
      head := controlKey
      kind := .improve
      watches := []
      writes := argumentSlots workload.roots },
    { key := sinkRuleKey
      head := sinkKey
      kind := .forward
      watches := argumentSlots (sinkArity workload)
      writes := [.result] }]

def applicationCount (workload : Workload) : Nat := workload.sinks + 1

def nodeCount (workload : Workload) : Nat := workload.roots + 1 + workload.sinks

def retainedCount (workload : Workload) : Nat :=
  1 + workload.sinks * workload.churn

def expectedDecisions (workload : Workload) : Nat :=
  1 + workload.sinks + workload.sinks * workload.churn

def expectedWakeAttempts (workload : Workload) : Nat :=
  if workload.dense then workload.roots * workload.sinks else workload.sinks

def expectedSuppressed (workload : Workload) : Nat :=
  expectedWakeAttempts workload - workload.sinks

/-- Larger ranks are strictly stronger synthetic facts. -/
def rankDomain : FactDomain Rank where
  top _ := 0
  narrow _ current candidate :=
    if current < candidate then .improved candidate else .noChange

def engineLimits (workload : Workload) : Experiment.Propagator.Limits :=
  let arity := Nat.max workload.roots (sinkArity workload)
  let applications := applicationCount workload
  { maxOperations := 3
    maxNodes := nodeCount workload
    maxRules := 2
    maxArity := arity
    maxApplications := applications
    maxQueueEntries := 4 * applications
    maxActions := 4 * applications + retainedCount workload
    maxAcceptedFacts := 4 * nodeCount workload
    maxRetainedSuggestions := retainedCount workload
    maxEffort := 1
    maxObservationValue := 1
    maxDiagnosticValue := 1
    maxOutcomeCandidates := Nat.max workload.roots 1
    maxOutcomeSuggestions := Nat.max workload.churn 1
    maxProposalItems := 0
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := nodeCount workload
    maxEqualities := 0
    splitEndpointLimit :=
      { maxEndpointHeight := 1, maxAlignmentShift := 0 } }

def policyLimits (workload : Workload) : Policy.Limits :=
  let backing := applicationCount workload + retainedCount workload
  let decisions := expectedDecisions workload
  { maxDecisions := decisions + 1
    maxTraversal := backing * (decisions + 3)
    maxLiveOffers := backing }

def candidate (node : NodeId) (fact : Rank) : Candidate Rank :=
  { node, fact, payload := { index := node.index } }

def maximumInput (inputs : List (FactView Rank)) : Rank :=
  inputs.foldl (fun current input => Nat.max current input.fact) 0

def churnSuggestions (workload : Workload) : List Suggestion :=
  (List.range workload.churn).map fun code =>
    .split
      { node := nodeId 0
        point := 0
        reason := .custom code }

/-- The companion registry gives meaning to the two opaque rule keys.  The
control's first run retains a retry; retrying it strengthens every root in one
atomic reply.  Sink calls are arbitrary unary or n-ary functions and emit
optional search suggestions only after that trigger. -/
def invoke (workload : Workload) (request : RuleRequest Rank) : Outcome Rank :=
  if request.action.key == controlRuleKey then
    if request.action.effort == 0 then
      .success [] [.retry 1]
        { arithmeticWork := 1, visitedEntries := 1, estimatedProofNodes := 1 }
    else
      .success ((rootIds workload).map fun root => candidate root 1) []
        { arithmeticWork := 1, visitedEntries := 1, estimatedProofNodes := 1 }
  else if request.action.key == sinkRuleKey then
    let input := maximumInput request.inputs
    .success [candidate request.action.node (input + 1)]
      (if input == 0 then [] else churnSuggestions workload)
      { arithmeticWork := 1, visitedEntries := 1, estimatedProofNodes := 1 }
  else
    .failed 1

/-- Build and saturate through the public engine request/reply API.  The only
live offer at policy adoption is the control retry; no fact, version, queue,
or metric field is patched by the fixture. -/
def prepare (workload : Workload) : Option (Policy.State Rank) := do
  if !workload.valid then none else pure ()
  let initial <-
    match Engine.start rankDomain (program workload) (rules workload)
        (Array.replicate (nodeCount workload) 0) (engineLimits workload) with
    | .ok engine => some engine
    | .error _ => none
  let driven := drive
    (fun (_ : Unit) request => (invoke workload request, ()))
    (applicationCount workload + 2) initial ()
  if driven.stop != .saturated || driven.state.suggestions.size != 1 then none
  else some (Policy.State.start driven.state (policyLimits workload))

/-! # One deterministic non-FIFO policy -/

structure Priority where
  tier : Nat
  index : Nat
  deriving DecidableEq, Repr

instance : Inhabited Priority := ⟨{ tier := 0, index := 0 }⟩

def classPriority : OfferClass -> Nat
  | .retry => 5
  | .invoke => 4
  | .equality => 3
  | .instantiate => 2
  | .split => 1

def offerIndex : OfferId -> Nat
  | .application application => application.index
  | .equality equality => equality.index
  | .suggestion suggestion => suggestion.index

def priorityOf (offer : OfferView) : Priority :=
  { tier := classPriority offer.offerClass, index := offerIndex offer.id }

def Priority.higher (left right : Priority) : Bool :=
  right.tier < left.tier ||
    (left.tier == right.tier && right.index < left.index)

def offerHigher (left right : OfferView) : Bool :=
  (priorityOf left).higher (priorityOf right)

/-- Select the maximum semantic offer and report exact policy comparisons.
This is intentionally not `offers[0]?`: both representations exercise a real
choice over the frontier. -/
def chooseMaximum (offers : Array OfferView) : Option OfferView × Nat := Id.run do
  let mut best : Option OfferView := none
  let mut comparisons := 0
  for offer in offers do
    match best with
    | none => best := some offer
    | some previous =>
        comparisons := comparisons + 1
        if offerHigher offer previous then best := some offer
  return (best, comparisons)

/-! # Maintained event-indexed max-heap -/

structure Entry where
  id : OfferId
  priority : Priority
  deriving DecidableEq, Repr

instance : Inhabited Entry :=
  ⟨{ id := .application (applicationId 0), priority := default }⟩

structure HeapCost where
  comparisons : Nat := 0
  moves : Nat := 0
  deriving DecidableEq, Repr

def HeapCost.add (left right : HeapCost) : HeapCost :=
  { comparisons := left.comparisons + right.comparisons
    moves := left.moves + right.moves }

structure Heap where
  entries : Array Entry := #[]
  deriving Repr

def swapEntries (entries : Array Entry) (left right : Nat) : Array Entry :=
  let leftEntry := entries[left]!
  let rightEntry := entries[right]!
  (entries.set! left rightEntry).set! right leftEntry

partial def siftUp (entries : Array Entry) (index : Nat) (cost : HeapCost) :
    Array Entry × HeapCost :=
  if index == 0 then (entries, cost)
  else
    let parent := (index - 1) / 2
    let cost := { cost with comparisons := cost.comparisons + 1 }
    if entries[index]!.priority.higher entries[parent]!.priority then
      siftUp (swapEntries entries index parent) parent
        { cost with moves := cost.moves + 2 }
    else
      (entries, cost)

def Heap.push (heap : Heap) (entry : Entry) : Heap × HeapCost :=
  let entries := heap.entries.push entry
  let (entries, cost) := siftUp entries (entries.size - 1) { moves := 1 }
  ({ entries }, cost)

partial def siftDown (entries : Array Entry) (index : Nat) (cost : HeapCost) :
    Array Entry × HeapCost :=
  let left := 2 * index + 1
  if entries.size <= left then (entries, cost)
  else
    let right := left + 1
    let (child, cost) :=
      if right < entries.size then
        let cost := { cost with comparisons := cost.comparisons + 1 }
        if entries[right]!.priority.higher entries[left]!.priority then
          (right, cost)
        else
          (left, cost)
      else
        (left, cost)
    let cost := { cost with comparisons := cost.comparisons + 1 }
    if entries[child]!.priority.higher entries[index]!.priority then
      siftDown (swapEntries entries child index) child
        { cost with moves := cost.moves + 2 }
    else
      (entries, cost)

def Heap.pop (heap : Heap) : Option (Entry × Heap × HeapCost) :=
  if heap.entries.isEmpty then none
  else
    let first := heap.entries[0]!
    if heap.entries.size == 1 then
      some (first, { entries := #[] }, { moves := 1 })
    else
      let last := heap.entries[heap.entries.size - 1]!
      let entries := (heap.entries.pop).set! 0 last
      let (entries, cost) := siftDown entries 0 { moves := 2 }
      some (first, { entries }, cost)

def Heap.ofOffers (offers : Array OfferView) : Heap × HeapCost := Id.run do
  let mut heap : Heap := {}
  let mut cost : HeapCost := {}
  for offer in offers do
    let (next, step) := heap.push { id := offer.id, priority := priorityOf offer }
    heap := next
    cost := cost.add step
  return (heap, cost)

/-! # Complete logical accounting -/

structure Work where
  /-- Backing application, equality, and retained-suggestion slots inspected
  by complete views. -/
  frontierSlots : Nat := 0
  /-- Live offers appended to complete view arrays. -/
  frontierEmits : Nat := 0
  /-- Application, equality, and suggestion clock slots rebuilt by
  each wrapper state advance. -/
  clockSyncSlots : Nat := 0
  /-- Suggestion clocks revisited by `pruneSuggestions` after an advance. -/
  suggestionPruneSlots : Nat := 0
  /-- Dependency watcher entries attempted, including suppressed insertions. -/
  dependencyVisits : Nat := 0
  /-- Newly appended queue and retained-suggestion events consumed by the
  maintained index. -/
  eventVisits : Nat := 0
  /-- Explicit `offer?` calls made by the maintained adapter. -/
  offerRechecks : Nat := 0
  /-- Engine-side semantic revalidations caused by select or dismiss. -/
  selectionRechecks : Nat := 0
  /-- Variable-length watched inputs and proposal items traversed while
  constructing or refreshing semantic keys, including successful suggestion
  checks performed by pruning. -/
  semanticItems : Nat := 0
  priorityComparisons : Nat := 0
  priorityMoves : Nat := 0
  deriving DecidableEq, Repr

def Work.total (work : Work) : Nat :=
  work.frontierSlots + work.frontierEmits + work.clockSyncSlots +
    work.suggestionPruneSlots + work.dependencyVisits + work.eventVisits +
    work.offerRechecks + work.selectionRechecks + work.semanticItems +
    work.priorityComparisons + work.priorityMoves

def retainedSemanticItems (retained : RetainedSuggestion) : Nat :=
  retained.action.inputs.length +
    match retained.suggestion with
    | .retry _ | .split _ => 0
    | .instantiate request =>
        request.nodes.length + request.equalities.length + request.scopes.length +
          (request.nodes.foldl (fun count node => count + node.args.length) 0) +
          (request.scopes.foldl (fun count scope =>
            count + 1 + scope.watches.length + scope.writes.length) 0)

def offerSemanticItems (state : Policy.State Fact) : OfferId -> Nat
  | .application application =>
      (state.engine.applications[application.index]?).map
        (fun value => value.watches.length) |>.getD 0
  | .equality _ => 2
  | .suggestion suggestion =>
      (state.engine.suggestions[suggestion.index]?).map retainedSemanticItems |>.getD 0

def offersSemanticItems (state : Policy.State Fact) (offers : Array OfferView) : Nat :=
  offers.foldl (fun count offer => count + offerSemanticItems state offer.id) 0

def pruneSemanticItems (state : Policy.State Fact) : Nat := Id.run do
  let mut count := 0
  for index in [0:state.suggestions.size] do
    match state.suggestions[index]?, state.engine.suggestions[index]? with
    | some clock, some retained =>
        if clock.active then count := count + retainedSemanticItems retained
    | _, _ => pure ()
  return count

def frontierBacking (state : Policy.State Fact) : Nat :=
  state.applications.size + state.equalities.size + state.suggestions.size

def Work.view (work : Work) (state : Policy.State Fact) (offers : Array OfferView) : Work :=
  { work with
    frontierSlots := work.frontierSlots + frontierBacking state
    frontierEmits := work.frontierEmits + offers.size
    semanticItems := work.semanticItems + offersSemanticItems state offers }

def Work.advance (work : Work) (state : Policy.State Fact) : Work :=
  { work with
    clockSyncSlots := work.clockSyncSlots + frontierBacking state
    suggestionPruneSlots := work.suggestionPruneSlots + state.suggestions.size
    semanticItems := work.semanticItems + pruneSemanticItems state }

def Work.heap (work : Work) (cost : HeapCost) : Work :=
  { work with
    priorityComparisons := work.priorityComparisons + cost.comparisons
    priorityMoves := work.priorityMoves + cost.moves }

def metricDelta (before after : Nat) : Nat := after - before

def Work.dependencies (work : Work) (before after : Engine Rank) : Work :=
  let inserted := metricDelta before.metrics.queueInsertions after.metrics.queueInsertions
  let suppressed :=
    metricDelta before.metrics.suppressedInsertions after.metrics.suppressedInsertions
  { work with dependencyVisits := work.dependencyVisits + inserted + suppressed }

def selectionFor (state : Policy.State Rank) (offer : OfferView) : Selection :=
  { scope := state.scope
    serial := state.serial
    programVersion := state.engine.programVersion
    id := offer.id
    expected := offer.key }

structure Step where
  state : Policy.State Rank
  work : Work

/-- Execute the common policy choice.  Invocation and retry offers call the
arbitrary registry, instantiations go through engine-owned structural
admission, and only optional split suggestions are dismissed. -/
def execute (workload : Workload) (state : Policy.State Rank)
    (offer : OfferView) (work : Work) : Option Step :=
  let selection := selectionFor state offer
  let work :=
    { work with
      selectionRechecks := work.selectionRechecks + 1
      semanticItems := work.semanticItems + offerSemanticItems state offer.id }
  match offer.offerClass with
  | .split =>
      match state.dismiss selection with
      | .completed .dismissed next => some { state := next, work }
      | _ => none
  | .instantiate =>
      let before := state.engine
      match state.select selection with
      | .completed completion next =>
          match completion with
          | .instanceAdmitted _ | .instanceDuplicate | .instanceRejected _ =>
              some
                { state := next
                  work := (work.advance next).dependencies before next.engine }
          | .dismissed => none
      | _ => none
  | .invoke | .retry =>
      match state.select selection with
      | .request request awaiting =>
          let work := work.advance awaiting
          let before := awaiting.engine
          match awaiting.submit (request.action.reply (invoke workload request)) with
          | .accepted _ next =>
              some
                { state := next
                  work := (work.advance next).dependencies before next.engine }
          | _ => none
      | _ => none
  | .equality => none

/-! # Complete-scan run -/

inductive Stop where
  | saturated
  | incomplete
  | setupFailure
  | frontierResource
  | invalidTransition
  | fuel
  deriving DecidableEq, Repr

structure Result where
  stop : Stop
  work : Work
  decisions : Nat
  calls : Nat
  improvements : Nat
  dismissals : Nat
  queueInsertions : Nat
  suppressedInsertions : Nat
  retainedSuggestions : Nat
  liveOffers : Nat
  facts : Array Rank
  versions : Array Nat
  history : Nat
  incomplete : Bool
  checksum : Nat
  choices : List OfferId
  deriving DecidableEq, Repr

def factsChecksum (facts : Array Rank) : Nat := Id.run do
  let mut checksum := 0
  for index in [0:facts.size] do
    checksum := checksum + (index + 1) * (facts[index]! + 1)
  return checksum

/-- Uncharged full scan used only as a post-run conformance oracle.  It is not
part of either representation's measured work. -/
def oracleLiveOffers (state : Policy.State Rank) : Nat := Id.run do
  let mut live := 0
  for index in [0:state.applications.size] do
    if (state.offer? (.application (applicationId index))).isSome then
      live := live + 1
  for index in [0:state.equalities.size] do
    if (state.offer? (.equality { index })).isSome then live := live + 1
  for index in [0:state.suggestions.size] do
    if (state.offer? (.suggestion (suggestionId index))).isSome then
      live := live + 1
  return live

def result (stop : Stop) (base state : Policy.State Rank) (work : Work)
    (choicesRev : List OfferId) : Result :=
  { stop
    work
    decisions := metricDelta base.metrics.decisions state.metrics.decisions
    calls := metricDelta base.engine.metrics.requests state.engine.metrics.requests
    improvements :=
      metricDelta base.engine.metrics.improvements state.engine.metrics.improvements
    dismissals := metricDelta base.metrics.dismissals state.metrics.dismissals
    queueInsertions :=
      metricDelta base.engine.metrics.queueInsertions state.engine.metrics.queueInsertions
    suppressedInsertions :=
      metricDelta base.engine.metrics.suppressedInsertions
        state.engine.metrics.suppressedInsertions
    retainedSuggestions := state.engine.suggestions.size - base.engine.suggestions.size
    liveOffers := oracleLiveOffers state
    facts := state.engine.facts
    versions := state.engine.versions
    history := state.engine.history.size - base.engine.history.size
    incomplete := state.incomplete
    checksum := factsChecksum state.engine.facts
    choices := choicesRev.reverse }

def failedResult (stop : Stop) : Result :=
  { stop
    work := {}
    decisions := 0
    calls := 0
    improvements := 0
    dismissals := 0
    queueInsertions := 0
    suppressedInsertions := 0
    retainedSuggestions := 0
    liveOffers := 0
    facts := #[]
    versions := #[]
    history := 0
    incomplete := false
    checksum := 0
    choices := [] }

def scanLoop (workload : Workload) (base : Policy.State Rank) :
    Nat -> Policy.State Rank -> Work -> List OfferId -> Result
  | 0, state, work, choices => result .fuel base state work choices
  | fuel + 1, state, work, choices =>
      match state.view with
      | .error _ => result .frontierResource base state work choices
      | .ok (view, scanned) =>
          let work := work.view state view.offers
          let (choice, comparisons) := chooseMaximum view.offers
          let work :=
            { work with
              priorityComparisons := work.priorityComparisons + comparisons }
          match choice with
          | none =>
              result (if scanned.incomplete then .incomplete else .saturated)
                base scanned work choices
          | some offer =>
              match execute workload scanned offer work with
              | none => result .invalidTransition base scanned work choices
              | some step => scanLoop workload base fuel step.state step.work
                  (offer.id :: choices)

@[noinline]
def runScanPrepared (workload : Workload) (state : Policy.State Rank) : Result :=
  scanLoop workload state (expectedDecisions workload + 2) state {} []

def runScan (workload : Workload) : Result :=
  match prepare workload with
  | none => failedResult .setupFailure
  | some state => runScanPrepared workload state

/-! # Maintained event-indexed run -/

structure Index where
  heap : Heap
  queueCursor : Nat
  suggestionCursor : Nat
  deriving Repr

def offerIdOfWork : WorkItem -> OfferId
  | .application application => .application application
  | .equality equality => .equality equality

def Index.seed (state : Policy.State Rank) : Except ViewError (Index × Policy.State Rank × Work) := do
  let (view, scanned) <- state.view
  let (heap, heapCost) := Heap.ofOffers view.offers
  let work := (({} : Work).view state view.offers).heap heapCost
  pure
    ({ heap
       queueCursor := state.engine.queue.size
       suggestionCursor := state.engine.suggestions.size },
     scanned, work)

/-- Consume exactly the newly appended work and suggestion suffixes.  The
engine's dirty bits and freshness guards remain authoritative: every event is
re-read through `offer?` before it enters the maintained heap. -/
def Index.sync (index : Index) (state : Policy.State Rank) (work : Work) :
    Index × Work := Id.run do
  let mut heap := index.heap
  let mut work := work
  for cursor in [index.queueCursor:state.engine.queue.size] do
    work :=
      { work with
        eventVisits := work.eventVisits + 1
        offerRechecks := work.offerRechecks + 1 }
    match state.engine.queue[cursor]? with
    | none => pure ()
    | some item =>
        match state.offer? (offerIdOfWork item) with
        | none => pure ()
        | some offer =>
            work :=
              { work with
                semanticItems := work.semanticItems + offerSemanticItems state offer.id }
            let (next, cost) := heap.push { id := offer.id, priority := priorityOf offer }
            heap := next
            work := work.heap cost
  for cursor in [index.suggestionCursor:state.engine.suggestions.size] do
    work :=
      { work with
        eventVisits := work.eventVisits + 1
        offerRechecks := work.offerRechecks + 1 }
    match state.offer? (.suggestion (suggestionId cursor)) with
    | none => pure ()
    | some offer =>
        work :=
          { work with
            semanticItems := work.semanticItems + offerSemanticItems state offer.id }
        let (next, cost) := heap.push { id := offer.id, priority := priorityOf offer }
        heap := next
        work := work.heap cost
  ({ heap
     queueCursor := state.engine.queue.size
     suggestionCursor := state.engine.suggestions.size },
   work)

def indexedLoop (workload : Workload) (base : Policy.State Rank) :
    Nat -> Policy.State Rank -> Index -> Work -> List OfferId -> Result
  | 0, state, _, work, choices => result .fuel base state work choices
  | fuel + 1, state, index, work, choices =>
      match index.heap.pop with
      | none =>
          result (if state.incomplete then .incomplete else .saturated)
            base state work choices
      | some (entry, heap, heapCost) =>
          let index := { index with heap }
          let work := (work.heap heapCost)
          let work := { work with offerRechecks := work.offerRechecks + 1 }
          match state.offer? entry.id with
          | none => indexedLoop workload base fuel state index work choices
          | some offer =>
              let work :=
                { work with
                  semanticItems := work.semanticItems + offerSemanticItems state offer.id }
              match execute workload state offer work with
              | none => result .invalidTransition base state work choices
              | some step =>
                  let (index, work) := index.sync step.state step.work
                  indexedLoop workload base fuel step.state index work (offer.id :: choices)

@[noinline]
def runIndexedPrepared (workload : Workload) (state : Policy.State Rank) : Result :=
  match Index.seed state with
  | .error _ => failedResult .frontierResource
  | .ok (index, seeded, work) =>
      indexedLoop workload state (3 * expectedDecisions workload + 3)
        seeded index work []

def runIndexed (workload : Workload) : Result :=
  match prepare workload with
  | none => failedResult .setupFailure
  | some state => runIndexedPrepared workload state

structure Comparison where
  scan : Result
  indexed : Result
  deriving DecidableEq, Repr

def comparePrepared (workload : Workload) (state : Policy.State Rank) : Comparison :=
  { scan := runScanPrepared workload state
    indexed := runIndexedPrepared workload state }

def compare (workload : Workload) : Comparison :=
  match prepare workload with
  | none => { scan := failedResult .setupFailure, indexed := failedResult .setupFailure }
  | some state => comparePrepared workload state

def expectedFacts (workload : Workload) : Array Rank := Id.run do
  let mut facts := #[]
  for _ in [0:workload.roots] do facts := facts.push 1
  facts := facts.push 0
  for _ in [0:workload.sinks] do facts := facts.push 2
  return facts

def expectedVersions (workload : Workload) : Array Nat := Id.run do
  let mut versions := #[]
  for _ in [0:workload.roots] do versions := versions.push 1
  versions := versions.push 0
  for _ in [0:workload.sinks] do versions := versions.push 2
  return versions

def semanticEqual (left right : Result) : Bool :=
  left.stop == right.stop && left.decisions == right.decisions &&
    left.calls == right.calls && left.improvements == right.improvements &&
    left.dismissals == right.dismissals &&
    left.queueInsertions == right.queueInsertions &&
    left.suppressedInsertions == right.suppressedInsertions &&
    left.retainedSuggestions == right.retainedSuggestions &&
    left.liveOffers == right.liveOffers && left.facts == right.facts &&
    left.versions == right.versions && left.history == right.history &&
    left.incomplete == right.incomplete && left.checksum == right.checksum &&
    left.choices == right.choices

def expectedResult (workload : Workload) (value : Result) : Bool :=
  value.stop == .saturated && value.decisions == expectedDecisions workload &&
    value.calls == workload.sinks + 1 &&
    value.improvements == workload.roots + workload.sinks &&
    value.dismissals == workload.sinks * workload.churn &&
    value.queueInsertions == workload.sinks &&
    value.suppressedInsertions == expectedSuppressed workload &&
    value.retainedSuggestions == workload.sinks * workload.churn &&
    value.liveOffers == 0 && value.facts == expectedFacts workload &&
    value.versions == expectedVersions workload &&
    value.history == workload.roots + workload.sinks && !value.incomplete &&
    value.checksum == factsChecksum (expectedFacts workload)

def comparisonValid (workload : Workload) (comparison : Comparison) : Bool :=
  workload.valid && semanticEqual comparison.scan comparison.indexed &&
    expectedResult workload comparison.scan && expectedResult workload comparison.indexed

/-- The first post-trigger choice is the highest application id, while the
FIFO queue contains the lowest sink id first.  This canary prevents the
indexed arm from degenerating back into a queue cursor. -/
def nonFifoChoice (workload : Workload) (result : Result) : Bool :=
  match result.choices with
  | .suggestion retry :: .application first :: _ =>
      retry == suggestionId 0 && first == applicationId workload.sinks &&
        workload.sinks != 1
  | _ => false

end Hex.Interval.Experiment.Propagator.PolicyFrontier
