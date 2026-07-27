/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Basic

@[expose] public section

/-!
# Function-agnostic propagation experiment

This module tests the request/reply boundary between an interval solver and
arbitrary function propagators.  The solver knows operation and rule keys, but
does not interpret either of them.  It owns only the expression DAG, current
facts, fact versions, dependency indexes, and deterministic resource counters.

A companion registry may keep caches of any Lean type.  It receives a
`RuleRequest` containing exactly the declared reads and writes, then replies
with an `Outcome` bound to that action.  Candidate facts are intersected by an
engine-owned `FactDomain`; function-specific code never enters the scheduler.

This is an experiment, not yet the supported `HexInterval` API.  Selecting a
retained expression proposal runs a separate atomic validator before extending
the live program and rebuilding its concrete rule applications.
-/

namespace Hex.Interval.Experiment.Propagator

/-! ## Typed expression program -/

/-- Compact domain identifier.  The initial corpus uses only the real domain,
but the scheduler does not assume that all nodes have the same type. -/
structure DomainId where
  index : Nat
  deriving DecidableEq, Repr

/-- Stable, versioned semantic operation name. -/
structure OpKey where
  name : String
  version : Nat := 1
  deriving DecidableEq, Repr

/-- Compact index into a program's operation table. -/
structure OpId where
  index : Nat
  deriving DecidableEq, Repr

/-- Compact index into a program's node table. -/
structure NodeId where
  index : Nat
  deriving DecidableEq, Repr

/-- An operation signature known to the typed frontend, but not interpreted by
the scheduler. -/
structure Operation where
  key : OpKey
  inputs : List DomainId
  output : DomainId
  deriving Repr

/-- One instruction in a typed single-assignment expression DAG. -/
structure Node where
  domain : DomainId
  op : OpId
  args : List NodeId
  deriving Repr

/-- Immutable base expression program. -/
structure Program where
  operations : Array Operation
  nodes : Array Node
  deriving Repr

namespace Program

/-- Exact optional operation lookup. -/
def operation? (program : Program) (operation : OpId) : Option Operation :=
  program.operations[operation.index]?

/-- Exact optional node lookup. -/
def node? (program : Program) (node : NodeId) : Option Node :=
  program.nodes[node.index]?

def uniqueOpKeys : List Operation -> Bool
  | [] => true
  | operation :: operations =>
      !(operations.any fun other => other.key == operation.key) &&
        uniqueOpKeys operations

def argsCheck (program : Program) (outputIndex : Nat) :
    List NodeId -> List DomainId -> Bool
  | [], [] => true
  | argument :: arguments, domain :: domains =>
      argument.index < outputIndex &&
        (program.node? argument).any (fun node => node.domain == domain) &&
        argsCheck program outputIndex arguments domains
  | _, _ => false

def nodeCheck (program : Program) (outputIndex : Nat) (node : Node) : Bool :=
  match program.operation? node.op with
  | none => false
  | some operation =>
      node.domain == operation.output &&
        argsCheck program outputIndex node.args operation.inputs

def nodesCheckFrom (program : Program) : Nat -> List Node -> Bool
  | _, [] => true
  | outputIndex, node :: nodes =>
      nodeCheck program outputIndex node && nodesCheckFrom program (outputIndex + 1) nodes

/-- Validate operation-key uniqueness, operation references, arities, domains,
and SSA topology. -/
def check (program : Program) : Bool :=
  uniqueOpKeys program.operations.toList && nodesCheckFrom program 0 program.nodes.toList

end Program

/-! ## Rule registration -/

/-- Stable rule name.  `schema` versions the proof payload understood by the
companion checker. -/
structure RuleKey where
  name : String
  schema : Nat := 1
  deriving DecidableEq, Repr

/-- Compact index into one registry snapshot. -/
structure RuleId where
  index : Nat
  deriving DecidableEq, Repr

/-- Compact index of a rule application to a particular expression node. -/
structure ApplicationId where
  index : Nat
  deriving DecidableEq, Repr

/-- Compact index of one admitted structural equality. -/
structure EqualityId where
  index : Nat
  deriving DecidableEq, Repr

/-- A single scheduler queue carries both companion-backed rule applications
and engine-owned equality contractors. -/
inductive WorkItem where
  | application (application : ApplicationId)
  | equality (equality : EqualityId)
  deriving DecidableEq, Repr

/-- Propagator roles are policy data, not operation semantics. -/
inductive ActionKind where
  | forward
  | backward
  | improve
  | shave
  | instantiate
  | rewrite
  | regularize
  | split
  deriving DecidableEq, Repr

/-- A registration names the result node or one of its arguments without
depending on concrete node identifiers. -/
inductive Slot where
  | result
  | argument (index : Nat)
  deriving DecidableEq, Repr

/-- One explicit propagator registration.  Several registrations may have the
same `head`; they remain independent methods with independent rule keys. -/
structure Registration where
  key : RuleKey
  head : OpKey
  kind : ActionKind
  watches : List Slot
  writes : List Slot
  initialEffort : Nat := 0
  deriving Repr

/-- A registration resolved against one concrete program node. -/
structure Application where
  rule : RuleId
  node : NodeId
  kind : ActionKind
  watches : List NodeId
  writes : List NodeId
  effort : Nat
  deriving Repr

def uniqueList [DecidableEq alpha] : List alpha -> Bool
  | [] => true
  | item :: items => !(items.contains item) && uniqueList items

def dedupListFrom [DecidableEq alpha] (seen : List alpha) : List alpha -> List alpha
  | [] => []
  | item :: items =>
      if seen.contains item then dedupListFrom seen items
      else item :: dedupListFrom (item :: seen) items

def dedupList [DecidableEq alpha] (items : List alpha) : List alpha :=
  dedupListFrom [] items

def uniqueRuleKeys : List Registration -> Bool
  | [] => true
  | rule :: rules =>
      !(rules.any fun other => other.key == rule.key) && uniqueRuleKeys rules

def opKeyExists (program : Program) (key : OpKey) : Bool :=
  program.operations.any fun operation => operation.key == key

def Program.operationWithKey? (program : Program) (key : OpKey) : Option Operation :=
  program.operations.toList.find? fun operation => operation.key == key

def Slot.validFor (operation : Operation) : Slot -> Bool
  | .result => true
  | .argument index => operation.inputs[index]?.isSome

def resolveSlot? (output : NodeId) (node : Node) : Slot -> Option NodeId
  | .result => some output
  | .argument index => node.args[index]?

def resolveSlots? (output : NodeId) (node : Node)
    (slots : List Slot) : Option (List NodeId) :=
  slots.mapM (resolveSlot? output node)

/-- Reject duplicate keys, unknown heads, duplicate watch/write slots, and
out-of-range slots.  Empty writes are valid for discovery and split rules. -/
def registrationsCheck (program : Program) (rules : Array Registration) : Bool :=
  uniqueRuleKeys rules.toList && rules.all fun rule =>
    match program.operationWithKey? rule.head with
    | none => false
    | some operation =>
        uniqueList rule.watches && uniqueList rule.writes &&
          rule.watches.all (Slot.validFor operation) &&
            rule.writes.all (Slot.validFor operation)

/-- Resolve every matching `(registration, node)` pair in node-major,
registration-minor order.  Operation keys are opaque to this compiler. -/
def compileApplications (program : Program) (rules : Array Registration) :
    Option (Array Application) := do
  if !program.check || !registrationsCheck program rules then
    none
  else
    let mut applications := #[]
    for nodeIndex in [0:program.nodes.size] do
      let node <- program.nodes[nodeIndex]?
      let operation <- program.operation? node.op
      for ruleIndex in [0:rules.size] do
        let rule <- rules[ruleIndex]?
        if rule.head == operation.key then
          let watches <- resolveSlots? { index := nodeIndex } node rule.watches
          let writes <- resolveSlots? { index := nodeIndex } node rule.writes
          applications := applications.push
            { rule := { index := ruleIndex }
              node := { index := nodeIndex }
              kind := rule.kind
              watches
              writes
              effort := rule.initialEffort }
    some applications

/-- Bounded application compiler.  Error `false` denotes an invalid program or
registry; error `true` denotes the exact application cap. -/
def compileApplicationsWithin (limit : Nat) (program : Program)
    (rules : Array Registration) : Except Bool (Array Application) := do
  if !program.check || !registrationsCheck program rules then
    throw false
  let mut applications := #[]
  for nodeIndex in [0:program.nodes.size] do
    let some node := program.nodes[nodeIndex]? | throw false
    let some operation := program.operation? node.op | throw false
    for ruleIndex in [0:rules.size] do
      let some rule := rules[ruleIndex]? | throw false
      if rule.head == operation.key then
        if limit <= applications.size then
          throw true
        let some watches := resolveSlots? { index := nodeIndex } node rule.watches
          | throw false
        let some writes := resolveSlots? { index := nodeIndex } node rule.writes
          | throw false
        applications := applications.push
          { rule := { index := ruleIndex }
            node := { index := nodeIndex }
            kind := rule.kind
            watches
            writes
            effort := rule.initialEffort }
  pure applications

/-! ## Request/reply protocol -/

/-- Monotone version observed for one watched fact. -/
structure SeenVersion where
  node : NodeId
  version : Nat
  deriving DecidableEq, Repr

/-- One scheduler request.  `serial` prevents a delayed registry reply from
being confused with a later invocation of the same rule. -/
structure Action where
  serial : Nat
  programVersion : Nat
  application : ApplicationId
  rule : RuleId
  key : RuleKey
  node : NodeId
  kind : ActionKind
  effort : Nat
  inputs : List SeenVersion
  deriving Repr

/-- Immutable fact view supplied with an action. -/
structure Snapshot (Fact : Type) where
  facts : Array Fact
  versions : Array Nat
  contradictory : Bool

namespace Snapshot

/-- Exact optional fact lookup. -/
def fact? (snapshot : Snapshot Fact) (node : NodeId) : Option Fact :=
  snapshot.facts[node.index]?

/-- Exact optional version lookup. -/
def version? (snapshot : Snapshot Fact) (node : NodeId) : Option Nat :=
  snapshot.versions[node.index]?

end Snapshot

/-- One declared rule input.  Propagators receive these projected views rather
than an unrestricted snapshot, so every semantic dependency has a watcher. -/
structure FactView (Fact : Type) where
  node : NodeId
  fact : Fact
  version : Nat

/-- Function-specific registry request with exactly the application's declared
inputs. -/
structure RuleRequest (Fact : Type) where
  action : Action
  inputs : List (FactView Fact)
  writes : List NodeId

namespace RuleRequest

/-- Lookup is restricted to declared inputs. -/
def fact? (request : RuleRequest Fact) (node : NodeId) : Option Fact :=
  (request.inputs.find? fun input => input.node == node).map (fun input => input.fact)

end RuleRequest

/-- Immutable proof payload allocated by the companion registry.  It is not a
pointer into a mutable propagator cache. -/
structure PayloadId where
  index : Nat
  deriving DecidableEq, Repr

/-- One proposed fact about an existing expression node. -/
structure Candidate (Fact : Type) where
  node : NodeId
  fact : Fact
  payload : PayloadId

/-- A reference in a proposed expression extension. -/
inductive NodeRef where
  | existing (node : NodeId)
  | proposed (index : Nat)
  deriving DecidableEq, Repr

/-- One SSA instruction proposed by a shape-triggered propagator. -/
structure ProposedNode where
  domain : DomainId
  op : OpId
  args : List NodeRef
  deriving Repr

/-- An equality proposed alongside new expressions.  This experiment retains
the opaque payload and endpoints as untrusted replay data; the edge is not
scheduler-active until a companion-backed activation transition is added. -/
structure ProposedEquality where
  left : NodeRef
  right : NodeRef
  payload : PayloadId
  deriving Repr

/-- Untrusted atomic expression-extension request.  The engine, not the rule,
recomputes generations and assigns concrete node identifiers. -/
structure InstantiationRequest where
  key : Nat
  triggers : List NodeId
  claimedGeneration : Nat
  nodes : List ProposedNode
  equalities : List ProposedEquality
  payload : PayloadId
  deriving Repr

/-- Why a propagator recommends a proof-state split. -/
inductive SplitReason where
  | singularity
  | totalityBoundary
  | kink
  | criticalPoint
  | contractor
  | smallLandmark
  | midpoint
  | custom (code : Nat)
  deriving DecidableEq, Repr

/-- A proof-split suggestion.  The engine alone creates complementary child
scopes; the rule supplies only a node, cut, and reason. -/
structure SplitRequest where
  node : NodeId
  point : Dyadic
  reason : SplitReason

/-- Non-fact information returned to the search policy. -/
inductive Suggestion where
  | retry (effort : Nat)
  | instantiate (request : InstantiationRequest)
  | split (request : SplitRequest)

/-- A policy candidate paired with engine-owned invocation provenance. -/
structure RetainedSuggestion where
  action : Action
  suggestion : Suggestion

/-- Engine-owned index of one retained policy suggestion. -/
structure SuggestionId where
  index : Nat
  deriving DecidableEq, Repr

/-- Deterministic logical work observations.  Wall time and allocation counts
are telemetry and do not belong here. -/
structure CostObservation where
  arithmeticWork : Nat := 0
  visitedEntries : Nat := 0
  estimatedProofNodes : Nat := 0
  deriving DecidableEq, Repr

/-- A rule reply.  Only `success` may contain facts or structural suggestions;
the other cases are precise negative observations for policy and diagnostics. -/
inductive Outcome (Fact : Type) where
  | success (candidates : List (Candidate Fact))
      (suggestions : List Suggestion) (cost : CostObservation)
  | noChange (cost : CostObservation)
  | inapplicable
  | resourceLimit (budget : Nat)
  | failed (code : Nat)

/-- Registry response bound to the exact outstanding invocation. -/
structure Reply (Fact : Type) where
  serial : Nat
  programVersion : Nat
  application : ApplicationId
  outcome : Outcome Fact

def Action.reply (action : Action) (outcome : Outcome Fact) : Reply Fact :=
  { serial := action.serial
    programVersion := action.programVersion
    application := action.application
    outcome }

/-! ## Fact intersection boundary -/

/-- Result of intersecting an untrusted candidate with the current strongest
fact.  The explicit record passed to `submit` supplies this operation; the
scheduler is independent of endpoint representation. -/
inductive NarrowResult (Fact : Type) where
  | noChange
  | improved (fact : Fact)
  | contradiction (fact : Fact)
  | malformed (code : Nat)
  | resourceLimit (budget : Nat)

/-- The only fact-domain behavior needed by propagation scheduling. -/
structure FactDomain (Fact : Type) where
  top : DomainId -> Fact
  narrow : DomainId -> Fact -> Fact -> NarrowResult Fact

/-- Bounded list check which inspects at most one constructor beyond the
trusted limit. -/
def listWithin {alpha : Type} : Nat -> List alpha -> Bool
  | _, [] => true
  | 0, _ :: _ => false
  | limit + 1, _ :: items => listWithin limit items

/-! ## Deterministic engine resources -/

/-- Solver-owned resource whose trusted limit was exhausted. -/
inductive Resource where
  | operations
  | nodes
  | rules
  | arity
  | applications
  | queueEntries
  | actions
  | acceptedFacts
  | retainedSuggestions
  | outcomeCandidates
  | outcomeSuggestions
  | instances
  | generation
  | equalities
  deriving DecidableEq, Repr

/-- Independent structural and work limits. -/
structure Limits where
  maxOperations : Nat
  maxNodes : Nat
  maxRules : Nat
  maxArity : Nat
  maxApplications : Nat
  maxQueueEntries : Nat
  maxActions : Nat
  maxAcceptedFacts : Nat
  maxRetainedSuggestions : Nat
  maxOutcomeCandidates : Nat
  maxOutcomeSuggestions : Nat
  maxProposalItems : Nat
  maxInstances : Nat
  maxGeneration : Nat
  maxEqualities : Nat
  splitEndpointLimit : EndpointLimit
  deriving DecidableEq, Repr

/-- Logical counters used both by conformance fixtures and later policy
experiments. -/
structure Metrics where
  queueInsertions : Nat := 0
  suppressedInsertions : Nat := 0
  queuePops : Nat := 0
  requests : Nat := 0
  replies : Nat := 0
  candidates : Nat := 0
  improvements : Nat := 0
  contradictions : Nat := 0
  ruleNoChange : Nat := 0
  ruleInapplicable : Nat := 0
  ruleResourceLimits : Nat := 0
  ruleFailures : Nat := 0
  admittedInstances : Nat := 0
  duplicateInstances : Nat := 0
  generatedNodes : Nat := 0
  generatedEqualities : Nat := 0
  equalityRuns : Nat := 0
  equalityImprovements : Nat := 0
  deriving DecidableEq, Repr

/-- Why one narrowed fact was admitted.  Equality transport is an engine
operation and therefore does not invent a registry rule or payload. -/
inductive FactCause where
  | rule (action : Action) (payload : PayloadId)
  | transport (equality : EqualityId) (source : SeenVersion)
  deriving Repr

/-- One retained fact provenance record. -/
structure FactEvent (Fact : Type) where
  programVersion : Nat
  node : NodeId
  previous : SeenVersion
  fact : Fact
  version : Nat
  cause : FactCause

/-- Canonical key for one shape-rule application in this scope-free first
experiment. -/
structure InstanceKey where
  rule : RuleKey
  family : Nat
  substitution : List NodeId
  products : List NodeId
  deriving DecidableEq, Repr

/-- Structurally retained equality edge.  Its opaque payload is replay data;
the engine uses only its typed endpoints for untrusted search propagation. -/
structure EqualityEdge where
  left : NodeId
  right : NodeId
  generation : Nat
  origin : Action
  payload : PayloadId

/-- Replay-facing provenance for one committed program extension. -/
structure InstanceEvent where
  /-- Program snapshot after this extension commits. -/
  programVersion : Nat
  origin : Action
  family : Nat
  substitution : List NodeId
  products : List NodeId
  newNodes : List NodeId
  generation : Nat
  equalities : List EqualityEdge
  payload : PayloadId

/-- Live state of the function-agnostic scheduler. -/
structure Engine (Fact : Type) where
  programVersion : Nat
  factDomain : FactDomain Fact
  program : Program
  rules : Array Registration
  applications : Array Application
  watchers : Array (List WorkItem)
  facts : Array Fact
  versions : Array Nat
  generations : Array Nat
  queue : Array WorkItem
  queueHead : Nat
  queued : Array Bool
  equalityQueued : Array Bool
  pending : Option Action
  history : Array (FactEvent Fact)
  suggestions : Array RetainedSuggestion
  instances : List InstanceKey
  instanceHistory : Array InstanceEvent
  equalities : Array EqualityEdge
  contradictory : Bool
  metrics : Metrics
  limits : Limits

/-- Failure while validating and compiling an initial engine snapshot. -/
inductive StartError where
  | invalidProgram
  | invalidRegistrations
  | wrongFactCount
  | resourceLimit (resource : Resource)
  deriving DecidableEq, Repr

/-- Build the dependency index in application order followed by equality order.
Each equality is one undirected contractor watching both endpoints. -/
def buildWatchers (nodeCount : Nat) (applications : Array Application)
    (equalities : Array EqualityEdge) : Option (Array (List WorkItem)) := do
  let mut watchers := Array.replicate nodeCount []
  for applicationIndex in [0:applications.size] do
    let application <- applications[applicationIndex]?
    for node in dedupList application.watches do
      let current <- watchers[node.index]?
      watchers := watchers.set! node.index
        (.application { index := applicationIndex } :: current)
  for equalityIndex in [0:equalities.size] do
    let equality <- equalities[equalityIndex]?
    for node in dedupList [equality.left, equality.right] do
      let current <- watchers[node.index]?
      watchers := watchers.set! node.index (.equality { index := equalityIndex } :: current)
  some (watchers.map List.reverse)

/-- Initial queue containing every compiled application exactly once. -/
def initialQueue (applicationCount : Nat) : Array WorkItem := Id.run do
  let mut queue := #[]
  for index in [0:applicationCount] do
    queue := queue.push (.application { index })
  queue

/-- Validate and compile an engine.  The caller supplies one initial fact per
node, ordinarily the domain top refined by source hypotheses. -/
def Engine.start (factDomain : FactDomain Fact) (program : Program) (rules : Array Registration)
    (facts : Array Fact) (limits : Limits) : Except StartError (Engine Fact) := do
  if limits.maxOperations < program.operations.size then
    throw (.resourceLimit .operations)
  if limits.maxNodes < program.nodes.size then
    throw (.resourceLimit .nodes)
  if limits.maxRules < rules.size then
    throw (.resourceLimit .rules)
  if program.operations.any (fun operation => !listWithin limits.maxArity operation.inputs) ||
      program.nodes.any (fun node => !listWithin limits.maxArity node.args) ||
      rules.any (fun rule => !listWithin (limits.maxArity + 1) rule.watches ||
        !listWithin (limits.maxArity + 1) rule.writes) then
    throw (.resourceLimit .arity)
  if facts.size != program.nodes.size then
    throw .wrongFactCount
  if !program.check then
    throw .invalidProgram
  if !registrationsCheck program rules then
    throw .invalidRegistrations
  let applications <-
    match compileApplicationsWithin limits.maxApplications program rules with
    | .ok applications => pure applications
    | .error false => throw .invalidRegistrations
    | .error true => throw (.resourceLimit .applications)
  if limits.maxQueueEntries < applications.size then
    throw (.resourceLimit .queueEntries)
  let some watchers := buildWatchers program.nodes.size applications #[]
    | throw .invalidRegistrations
  pure
    { factDomain
      program
      programVersion := 0
      rules
      applications
      watchers
      facts
      versions := Array.replicate facts.size 0
      generations := Array.replicate facts.size 0
      queue := initialQueue applications.size
      queueHead := 0
      queued := Array.replicate applications.size true
      equalityQueued := #[]
      pending := none
      history := #[]
      suggestions := #[]
      instances := []
      instanceHistory := #[]
      equalities := #[]
      contradictory := false
      metrics := { queueInsertions := applications.size }
      limits }

/-! ## Incremental scheduling -/

namespace Engine

/-- Immutable view supplied to the companion registry. -/
def snapshot (state : Engine Fact) : Snapshot Fact :=
  { facts := state.facts
    versions := state.versions
    contradictory := state.contradictory }

/-- Read the versions of exactly the watched nodes in registration order. -/
def seenVersions? (state : Engine Fact) : List NodeId -> Option (List SeenVersion)
  | [] => some []
  | node :: nodes => do
      let version <- state.versions[node.index]?
      let rest <- seenVersions? state nodes
      some ({ node, version } :: rest)

/-- Project exactly the declared watched facts into a registry request. -/
def factViews? (state : Engine Fact) : List NodeId -> Option (List (FactView Fact))
  | [] => some []
  | node :: nodes => do
      let fact <- state.facts[node.index]?
      let version <- state.versions[node.index]?
      let rest <- factViews? state nodes
      some ({ node, fact, version } :: rest)

/-- Insert work unless it is already dirty.  The queue is an append-only work
log in this experiment, so its trusted cap also bounds total dependency churn. -/
def enqueue (state : Engine Fact) (work : WorkItem) : Except Resource (Engine Fact) := do
  let alreadyQueued <- match work with
    | .application application =>
        let some queued := state.queued[application.index]? | throw .applications
        pure queued
    | .equality equality =>
        let some queued := state.equalityQueued[equality.index]? | throw .equalities
        pure queued
  if alreadyQueued then
    pure
      { state with
        metrics :=
          { state.metrics with
            suppressedInsertions := state.metrics.suppressedInsertions + 1 } }
  else if state.limits.maxQueueEntries <= state.queue.size then
    throw .queueEntries
  else
    let state <- match work with
      | .application application =>
          pure { state with queued := state.queued.set! application.index true }
      | .equality equality =>
          pure { state with equalityQueued := state.equalityQueued.set! equality.index true }
    pure
      { state with
        queue := state.queue.push work
        metrics :=
          { state.metrics with
            queueInsertions := state.metrics.queueInsertions + 1 } }

/-- Wake precisely the applications registered on one changed node. -/
def wakeNode (state : Engine Fact) (node : NodeId) :
    Except Resource (Engine Fact) := do
  let some applications := state.watchers[node.index]?
    | throw .nodes
  applications.foldlM enqueue state

/-- Wake the union of dependencies after every fact in one outcome has been
installed.  Queue suppression ensures that a multi-output contractor creates
at most one pending call per affected application. -/
def wakeNodes (state : Engine Fact) (nodes : List NodeId) :
    Except Resource (Engine Fact) :=
  nodes.foldlM wakeNode state

end Engine

/-- Result of asking the engine for its next action.  Equality work is returned
as an internal step and never crosses the companion registry boundary. -/
inductive Poll (Fact : Type) where
  | request (request : RuleRequest Fact) (state : Engine Fact)
  | equality (equality : EqualityId) (state : Engine Fact)
  | saturated (state : Engine Fact)
  | contradiction (state : Engine Fact)
  | awaitingReply (state : Engine Fact)
  | resourceLimit (resource : Resource) (state : Engine Fact)
  | invalidState (state : Engine Fact)

namespace Engine

/-- Pop the next dirty work item.  Rule work freezes watched versions in an
action; equality work remains wholly inside the engine. -/
def poll (state : Engine Fact) : Poll Fact :=
  if state.pending.isSome then
    .awaitingReply state
  else if state.contradictory then
    .contradiction state
  else if state.queue.size <= state.queueHead then
    .saturated state
  else if state.limits.maxActions <= state.metrics.queuePops then
    .resourceLimit .actions state
  else
    match state.queue[state.queueHead]? with
    | none => .invalidState state
    | some (.equality equalityId) =>
        match state.equalities[equalityId.index]?, state.equalityQueued[equalityId.index]? with
        | some _, some true =>
            .equality equalityId
              { state with
                queueHead := state.queueHead + 1
                equalityQueued := state.equalityQueued.set! equalityId.index false
                metrics :=
                  { state.metrics with
                    queuePops := state.metrics.queuePops + 1
                    equalityRuns := state.metrics.equalityRuns + 1 } }
        | _, _ => .invalidState state
    | some (.application applicationId) =>
        match state.applications[applicationId.index]?,
            state.queued[applicationId.index]? with
        | some application, some true =>
            match state.rules[application.rule.index]?, state.seenVersions? application.watches,
                state.factViews? application.watches with
            | some rule, some inputs, some views =>
                let action : Action :=
                  { serial := state.metrics.requests
                    programVersion := state.programVersion
                    application := applicationId
                    rule := application.rule
                    key := rule.key
                    node := application.node
                    kind := application.kind
                    effort := application.effort
                    inputs }
                let next : Engine Fact :=
                  { state with
                    queueHead := state.queueHead + 1
                    queued := state.queued.set! applicationId.index false
                    pending := some action
                    metrics :=
                      { state.metrics with
                        queuePops := state.metrics.queuePops + 1
                        requests := state.metrics.requests + 1 } }
                .request { action, inputs := views, writes := application.writes } next
            | _, _, _ => .invalidState state
        | _, _ => .invalidState state

end Engine

/-! ## Atomic outcome admission -/

/-- Invalid registry reply.  These failures identify a broken registration or
an untrusted malformed outcome; none can establish a theorem. -/
inductive ReplyError where
  | noPendingAction
  | mismatchedAction
  | tooManyCandidates
  | tooManySuggestions
  | oversizedProposal
  | duplicateWrite
  | undeclaredWrite (node : NodeId)
  | missingFact (node : NodeId)
  | malformedFact (code : Nat)
  deriving DecidableEq, Repr

/-- Result of atomically admitting one reply. -/
inductive ReplyResult (Fact : Type) where
  | accepted (state : Engine Fact)
  | invalid (error : ReplyError) (state : Engine Fact)
  | resourceLimit (resource : Resource) (state : Engine Fact)
  | factResourceLimit (budget : Nat) (state : Engine Fact)

/-- One endpoint update computed by an equality contractor from a common
pre-step snapshot. -/
structure TransportUpdate (Fact : Type) where
  target : NodeId
  previous : SeenVersion
  source : SeenVersion
  fact : Fact
  contradiction : Bool

inductive EqualityFactError where
  | malformed (code : Nat)
  | resourceLimit (budget : Nat)

/-- Equality contractors are internal, atomic scheduler transitions. -/
inductive EqualityResult (Fact : Type) where
  | advanced (state : Engine Fact)
  | invalid (code : Nat) (state : Engine Fact)
  | resourceLimit (resource : Resource) (state : Engine Fact)
  | factResourceLimit (budget : Nat) (state : Engine Fact)

def existingRefBounded (nodeCount : Nat) : NodeRef -> Bool
  | .existing node => node.index < nodeCount
  | .proposed _ => true

def proposalBounded (nodeCount limit : Nat) (request : InstantiationRequest) : Bool :=
  listWithin limit request.triggers && listWithin limit request.nodes &&
    listWithin limit request.equalities &&
    request.nodes.all (fun node => listWithin limit node.args &&
      node.args.all (existingRefBounded nodeCount)) &&
    request.equalities.all (fun edge =>
      existingRefBounded nodeCount edge.left && existingRefBounded nodeCount edge.right)

def suggestionBounded (limits : Limits) (nodeCount : Nat) : Suggestion -> Bool
  | .retry _ => true
  | .split request =>
      request.node.index < nodeCount &&
        (EndpointCost.ofDyadic request.point).allowed limits.splitEndpointLimit
  | .instantiate request =>
      proposalBounded nodeCount limits.maxProposalItems request &&
        request.triggers.all fun node => node.index < nodeCount

def suggestionsBounded (limits : Limits) (nodeCount : Nat)
    (suggestions : List Suggestion) : Bool :=
  suggestions.all (suggestionBounded limits nodeCount)

namespace Engine

/-- Clear the request/reply latch and charge the registry reply. -/
def finishReply (state : Engine Fact) : Engine Fact :=
  { state with
    pending := none
    metrics := { state.metrics with replies := state.metrics.replies + 1 } }

def outcomeNegative (state : Engine Fact) (outcome : Outcome Fact) : Engine Fact :=
  let state := state.finishReply
  match outcome with
  | .noChange _ =>
      { state with
        metrics := { state.metrics with ruleNoChange := state.metrics.ruleNoChange + 1 } }
  | .inapplicable =>
      { state with
        metrics :=
          { state.metrics with ruleInapplicable := state.metrics.ruleInapplicable + 1 } }
  | .resourceLimit _ =>
      { state with
        metrics :=
          { state.metrics with
            ruleResourceLimits := state.metrics.ruleResourceLimits + 1 } }
  | .failed _ =>
      { state with
        metrics := { state.metrics with ruleFailures := state.metrics.ruleFailures + 1 } }
  | .success _ _ _ => state

def candidateNodesUnique (candidates : List (Candidate Fact)) : Bool :=
  uniqueList (candidates.map (fun candidate => candidate.node))

def candidatesAuthorized (writes : List NodeId) (candidates : List (Candidate Fact)) :
    Option ReplyError :=
  match candidates.find? (fun candidate => !(writes.contains candidate.node)) with
  | some candidate => some (.undeclaredWrite candidate.node)
  | none => none

def installImprovement (action : Action) (candidate : Candidate Fact)
    (fact : Fact) (contradiction : Bool) (state : Engine Fact) :
    Except (ReplyError × Option Nat × Option Resource) (Engine Fact) := do
  if state.limits.maxAcceptedFacts <= state.history.size then
    throw (.malformedFact 0, none, some .acceptedFacts)
  else
    let version := state.versions[candidate.node.index]! + 1
    let previous : SeenVersion :=
      { node := candidate.node, version := state.versions[candidate.node.index]! }
    pure
      { state with
        facts := state.facts.set! candidate.node.index fact
        versions := state.versions.set! candidate.node.index version
        history := state.history.push
          { programVersion := action.programVersion
            node := candidate.node
            previous
            fact
            version
            cause := .rule action candidate.payload }
        contradictory := state.contradictory || contradiction
        metrics :=
          { state.metrics with
            improvements := state.metrics.improvements + 1
            contradictions :=
              state.metrics.contradictions + if contradiction then 1 else 0 } }

/-- Install candidates without waking dependencies.  On failure, the caller
discards the returned working state and keeps the reply-cleared base state. -/
def installCandidates (action : Action) :
    Engine Fact -> List (Candidate Fact) ->
      Except (ReplyError × Option Nat × Option Resource) (Engine Fact × List NodeId)
  | state, [] => pure (state, [])
  | state, candidate :: candidates => do
      let some current := state.facts[candidate.node.index]?
        | throw (.missingFact candidate.node, none, none)
      let some target := state.program.node? candidate.node
        | throw (.missingFact candidate.node, none, none)
      let next <-
        match state.factDomain.narrow target.domain current candidate.fact with
        | .noChange => pure state
        | .malformed code => throw (.malformedFact code, none, none)
        | .resourceLimit budget => throw (.malformedFact 0, some budget, none)
        | .improved fact => installImprovement action candidate fact false state
        | .contradiction fact => installImprovement action candidate fact true state
      let (next, changed) <- installCandidates action next candidates
      let changed :=
        if next.versions[candidate.node.index]! == state.versions[candidate.node.index]! then
          changed
        else
          candidate.node :: changed
      pure (next, changed)

/-- Validate and atomically admit one rule reply.  Candidate facts are all
installed before the union of affected dependencies is woken. -/
def submit (state : Engine Fact) (reply : Reply Fact) : ReplyResult Fact :=
  match state.pending with
  | none => .invalid .noPendingAction state
  | some action =>
      if reply.serial != action.serial || reply.programVersion != action.programVersion ||
          reply.application != action.application then
        .invalid .mismatchedAction state
      else
      match reply.outcome with
      | .noChange _ | .inapplicable | .resourceLimit _ | .failed _ =>
          .accepted (state.outcomeNegative reply.outcome)
      | .success candidates suggestions _ =>
          let base := state.finishReply
          if !listWithin state.limits.maxOutcomeCandidates candidates then
            .invalid .tooManyCandidates base
          else if !listWithin state.limits.maxOutcomeSuggestions suggestions then
            .invalid .tooManySuggestions base
          else if !suggestionsBounded state.limits state.program.nodes.size suggestions then
            .invalid .oversizedProposal base
          else if !candidateNodesUnique candidates then
            .invalid .duplicateWrite base
          else
            match state.applications[action.application.index]? with
            | none => .invalid (.missingFact action.node) base
            | some application =>
                match candidatesAuthorized application.writes candidates with
                | some error => .invalid error base
                | none =>
                    if state.limits.maxRetainedSuggestions <
                        state.suggestions.size + suggestions.length then
                      .resourceLimit .retainedSuggestions base
                    else
                      let working : Engine Fact :=
                        { base with
                          suggestions := suggestions.foldl
                            (fun retained suggestion => retained.push
                              { action, suggestion })
                            base.suggestions
                          metrics :=
                            { base.metrics with
                              candidates := base.metrics.candidates + candidates.length } }
                      match installCandidates action working candidates with
                      | .error (_, some budget, _) =>
                          .factResourceLimit budget base
                      | .error (_, _, some resource) => .resourceLimit resource base
                      | .error (error, _, _) => .invalid error base
                      | .ok (working, changed) =>
                          match working.wakeNodes changed with
                          | .error resource => .resourceLimit resource base
                          | .ok next => .accepted next

def transportUpdate (target source : NodeId) (targetVersion sourceVersion : Nat) :
    NarrowResult Fact -> Except EqualityFactError (Option (TransportUpdate Fact))
  | .noChange => pure none
  | .improved fact =>
      pure (some
        { target
          previous := { node := target, version := targetVersion }
          source := { node := source, version := sourceVersion }
          fact
          contradiction := false })
  | .contradiction fact =>
      pure (some
        { target
          previous := { node := target, version := targetVersion }
          source := { node := source, version := sourceVersion }
          fact
          contradiction := true })
  | .malformed code => throw (.malformed code)
  | .resourceLimit budget => throw (.resourceLimit budget)

/-- Install one already-preflighted transport update without waking. -/
def installTransport (equality : EqualityId) (update : TransportUpdate Fact)
    (state : Engine Fact) : Engine Fact :=
  let version := update.previous.version + 1
  { state with
    facts := state.facts.set! update.target.index update.fact
    versions := state.versions.set! update.target.index version
    history := state.history.push
      { programVersion := state.programVersion
        node := update.target
        previous := update.previous
        fact := update.fact
        version
        cause := .transport equality update.source }
    contradictory := state.contradictory || update.contradiction
    metrics :=
      { state.metrics with
        improvements := state.metrics.improvements + 1
        equalityImprovements := state.metrics.equalityImprovements + 1
        contradictions :=
          state.metrics.contradictions + if update.contradiction then 1 else 0 } }

/-- Contract both endpoints of one admitted equality against the same facts,
commit all improvements together, then wake their dependency union. -/
def contractEquality (state : Engine Fact) (equalityId : EqualityId) :
    EqualityResult Fact :=
  match state.equalities[equalityId.index]? with
  | none => .invalid 0 state
  | some equality =>
      match state.program.node? equality.left, state.program.node? equality.right,
          state.facts[equality.left.index]?, state.facts[equality.right.index]?,
          state.versions[equality.left.index]?, state.versions[equality.right.index]? with
      | some leftNode, some rightNode, some leftFact, some rightFact,
          some leftVersion, some rightVersion =>
          if leftNode.domain != rightNode.domain then
            .invalid 1 state
          else
            let updates : Except EqualityFactError (List (TransportUpdate Fact)) := do
              let left <- transportUpdate equality.left equality.right leftVersion rightVersion
                (state.factDomain.narrow leftNode.domain leftFact rightFact)
              let right <- transportUpdate equality.right equality.left rightVersion leftVersion
                (state.factDomain.narrow leftNode.domain rightFact leftFact)
              pure ([left, right].filterMap id)
            match updates with
            | .error (.malformed code) => .invalid code state
            | .error (.resourceLimit budget) => .factResourceLimit budget state
            | .ok updates =>
                if state.limits.maxAcceptedFacts < state.history.size + updates.length then
                  .resourceLimit .acceptedFacts state
                else
                  let working := updates.foldl
                    (fun state update => installTransport equalityId update state) state
                  let changed := updates.map fun update => update.target
                  match working.wakeNodes changed with
                  | .error resource => .resourceLimit resource state
                  | .ok next => .advanced next
      | _, _, _, _, _, _ => .invalid 2 state

end Engine

/-! ## External registry driver -/

/-- Why a bounded request/reply run stopped. -/
inductive RunStop where
  | saturated
  | contradiction
  | engineResource (resource : Resource)
  | factResource (budget : Nat)
  | invalidReply (error : ReplyError)
  | invalidEngine
  | driverFuel
  deriving DecidableEq, Repr

/-- A run returns both solver state and the registry's arbitrary private cache. -/
structure RunResult (Fact Cache : Type) where
  state : Engine Fact
  cache : Cache
  stop : RunStop

/-- Execute the request/reply protocol with a registry-owned cache.  `invoke`
is the only place where operation or rule keys acquire function-specific
meaning. -/
def drive (invoke : Cache -> RuleRequest Fact -> Outcome Fact × Cache) :
    Nat -> Engine Fact -> Cache -> RunResult Fact Cache
  | 0, state, cache => { state, cache, stop := .driverFuel }
  | fuel + 1, state, cache =>
      match state.poll with
      | .request request awaiting =>
          let (outcome, cache) := invoke cache request
          match awaiting.submit (request.action.reply outcome) with
          | .accepted next => drive invoke fuel next cache
          | .invalid error next => { state := next, cache, stop := .invalidReply error }
          | .resourceLimit resource next =>
              { state := next, cache, stop := .engineResource resource }
          | .factResourceLimit budget next =>
              { state := next, cache, stop := .factResource budget }
      | .saturated state => { state, cache, stop := .saturated }
      | .contradiction state => { state, cache, stop := .contradiction }
      | .resourceLimit resource state =>
          { state, cache, stop := .engineResource resource }
      | .equality equality state =>
          match state.contractEquality equality with
          | .advanced next => drive invoke fuel next cache
          | .invalid _ next => { state := next, cache, stop := .invalidEngine }
          | .resourceLimit resource next =>
              { state := next, cache, stop := .engineResource resource }
          | .factResourceLimit budget next =>
              { state := next, cache, stop := .factResource budget }
      | .awaitingReply state | .invalidState state =>
          { state, cache, stop := .invalidEngine }

/-! ## Atomic expression instantiation -/

/-- Structural failure while validating a retained instantiation request. -/
inductive AdmissionError where
  | notInstantiation
  | pendingReply
  | missingSuggestion
  | staleSuggestion (proposed current : Nat)
  | oversizedProposal
  | badReferenceOrShape
  | generationMismatch (claimed actual : Nat)
  | invalidEquality
  | invalidCompiledProgram
  deriving DecidableEq, Repr

/-- Result of selecting one retained instantiation suggestion. -/
inductive AdmissionResult (Fact : Type) where
  | admitted (newNodes : List NodeId) (state : Engine Fact)
  | duplicate (state : Engine Fact)
  | invalid (error : AdmissionError) (state : Engine Fact)
  | resourceLimit (resource : Resource) (state : Engine Fact)

namespace Node

/-- Exact syntactic node equality used by the experiment's linear CSE table. -/
def same (left right : Node) : Bool :=
  left.domain == right.domain && left.op == right.op && left.args == right.args

end Node

/-- Linear reference CSE lookup.  The experiment measures this against indexed
tables before selecting a production representation. -/
def findNodeFrom : Nat -> List Node -> Node -> Option NodeId
  | _, [], _ => none
  | index, node :: nodes, target =>
      if node.same target then some { index } else findNodeFrom (index + 1) nodes target

def Program.findNode? (program : Program) (target : Node) : Option NodeId :=
  findNodeFrom 0 program.nodes.toList target

/-- Resolve a draft reference.  `existing` IDs are restricted to the immutable
pre-proposal boundary; generated references use prior draft positions. -/
def resolveRef? (baseSize : Nat) (resolved : List NodeId) : NodeRef -> Option NodeId
  | .existing node => if node.index < baseSize then some node else none
  | .proposed index => resolved[index]?

def resolveRefs? (baseSize : Nat) (resolved : List NodeId)
    (refs : List NodeRef) : Option (List NodeId) :=
  refs.mapM (resolveRef? baseSize resolved)

/-- Resolve draft nodes in order, validate each typed SSA instruction, and CSE
against both old nodes and earlier new nodes. -/
def resolveDrafts (baseSize : Nat) :
    Program -> List NodeId -> List ProposedNode -> Option (Program × List NodeId)
  | program, resolved, [] => some (program, resolved)
  | program, resolved, draft :: drafts => do
      let args <- resolveRefs? baseSize resolved draft.args
      let candidate : Node := { domain := draft.domain, op := draft.op, args }
      if !Program.nodeCheck program program.nodes.size candidate then
        none
      else
        let id := program.findNode? candidate |>.getD { index := program.nodes.size }
        let program :=
          if id.index < program.nodes.size then program
          else { program with nodes := program.nodes.push candidate }
        resolveDrafts baseSize program (resolved ++ [id]) drafts

/-- Existing references named directly by one draft reference list. -/
def existingRefs (refs : List NodeRef) : List NodeId :=
  refs.foldr (fun ref nodes => match ref with
    | .existing node => node :: nodes
    | .proposed _ => nodes) []

def requestExistingRefs (request : InstantiationRequest) : List NodeId :=
  request.triggers ++ request.nodes.flatMap (fun node => existingRefs node.args) ++
    request.equalities.flatMap (fun edge => existingRefs [edge.left, edge.right])

/-- Recompute instantiation depth from every old node used directly or reached
through a CSE hit. -/
def inferredGeneration? (generations : Array Nat) (baseSize : Nat)
    (request : InstantiationRequest) (resolved : List NodeId) : Option Nat := do
  let references := requestExistingRefs request ++ resolved.filter (fun node => node.index < baseSize)
  let mut greatest := 0
  for node in references do
    let generation <- generations[node.index]?
    greatest := Nat.max greatest generation
  some (greatest + 1)

/-- Treat equality endpoints as unordered for structural deduplication. -/
def EqualityEdge.sameEndpoints (edge : EqualityEdge) (left right : NodeId) : Bool :=
  (edge.left == left && edge.right == right) ||
    (edge.left == right && edge.right == left)

def resolveEqualities (baseSize generation : Nat) (origin : Action) (program : Program)
    (resolved : List NodeId) (existing : Array EqualityEdge) :
    List ProposedEquality -> Option (List EqualityEdge)
  | [] => some []
  | proposal :: proposals => do
      let left <- resolveRef? baseSize resolved proposal.left
      let right <- resolveRef? baseSize resolved proposal.right
      let leftNode <- program.node? left
      let rightNode <- program.node? right
      if left == right || leftNode.domain != rightNode.domain then
        none
      else
        let rest <- resolveEqualities baseSize generation origin program resolved existing proposals
        let duplicateExisting := existing.any fun edge => edge.sameEndpoints left right
        let duplicateNew := rest.any fun edge => edge.sameEndpoints left right
        if duplicateExisting || duplicateNew then
          some rest
        else
          some ({ left, right, generation, origin, payload := proposal.payload } :: rest)

def newNodeIds (baseSize totalSize : Nat) : List NodeId :=
  (List.range (totalSize - baseSize)).map fun offset => { index := baseSize + offset }

/-- Domain-correct top facts for a newly appended node suffix. -/
def newTopFacts (domain : FactDomain Fact) (baseSize : Nat)
    (nodes : Array Node) : Array Fact :=
  ((nodes.toList.drop baseSize).map fun node => domain.top node.domain).toArray

/-- Queue every newly compiled concrete application. -/
def enqueueNewApplications (oldCount newCount : Nat) (state : Engine Fact) :
    Except Resource (Engine Fact) :=
  (List.range newCount).foldlM
    (fun state offset => state.enqueue (.application { index := oldCount + offset })) state

/-- Queue every newly admitted equality contractor. -/
def enqueueNewEqualities (oldCount newCount : Nat) (state : Engine Fact) :
    Except Resource (Engine Fact) :=
  (List.range newCount).foldlM
    (fun state offset => state.enqueue (.equality { index := oldCount + offset })) state

namespace Engine

/-- Validate and commit one shape-triggered program extension.  Every derived
table is built on a temporary state; any failure returns the original engine. -/
def admitRetained (state : Engine Fact)
    (retained : RetainedSuggestion) : AdmissionResult Fact :=
  if state.pending.isSome then
    .invalid .pendingReply state
  else
    match retained.suggestion with
    | .retry _ | .split _ => .invalid .notInstantiation state
    | .instantiate request =>
        if !proposalBounded state.program.nodes.size state.limits.maxProposalItems request then
          .invalid .oversizedProposal state
        else
          let baseSize := state.program.nodes.size
          match resolveDrafts baseSize state.program [] request.nodes with
          | none => .invalid .badReferenceOrShape state
          | some (program, resolved) =>
              let instanceKey : InstanceKey :=
                { rule := retained.action.key
                  family := request.key
                  substitution := request.triggers
                  products := resolved }
              if state.instances.contains instanceKey then
                .duplicate
                  { state with
                    metrics :=
                      { state.metrics with
                        duplicateInstances := state.metrics.duplicateInstances + 1 } }
              else if retained.action.programVersion != state.programVersion then
                .invalid (.staleSuggestion retained.action.programVersion state.programVersion) state
              else if state.limits.maxInstances <= state.instances.length then
                .resourceLimit .instances state
              else
                match inferredGeneration? state.generations baseSize request resolved with
                | none => .invalid .badReferenceOrShape state
                | some generation =>
                    if request.claimedGeneration != generation then
                      .invalid (.generationMismatch request.claimedGeneration generation) state
                    else if state.limits.maxGeneration < generation then
                      .resourceLimit .generation state
                    else if state.limits.maxNodes < program.nodes.size then
                      .resourceLimit .nodes state
                    else
                      match resolveEqualities baseSize generation retained.action program resolved
                          state.equalities request.equalities with
                      | none => .invalid .invalidEquality state
                      | some equalities =>
                          if state.limits.maxEqualities <
                              state.equalities.size + equalities.length then
                            .resourceLimit .equalities state
                          else
                            match compileApplicationsWithin state.limits.maxApplications
                                program state.rules with
                            | .error false => .invalid .invalidCompiledProgram state
                            | .error true => .resourceLimit .applications state
                            | .ok applications =>
                                if applications.size < state.applications.size then
                                  .invalid .invalidCompiledProgram state
                                else
                                  let addedApplications :=
                                    applications.size - state.applications.size
                                  if state.limits.maxQueueEntries <
                                      state.queue.size + addedApplications + equalities.length then
                                    .resourceLimit .queueEntries state
                                  else
                                    let allEqualities := state.equalities ++ equalities.toArray
                                    match buildWatchers program.nodes.size applications
                                        allEqualities with
                                    | none => .invalid .invalidCompiledProgram state
                                    | some watchers =>
                                        let addedNodes := program.nodes.size - baseSize
                                        let generated := newNodeIds baseSize program.nodes.size
                                        let queued := state.queued ++
                                          Array.replicate addedApplications false
                                        let equalityQueued := state.equalityQueued ++
                                          Array.replicate equalities.length false
                                        let prospective : Engine Fact :=
                                          { state with
                                            programVersion := state.programVersion + 1
                                            program
                                            applications
                                            watchers
                                            facts := state.facts ++
                                              newTopFacts state.factDomain baseSize program.nodes
                                            versions := state.versions ++
                                              Array.replicate addedNodes 0
                                            generations := state.generations ++
                                              Array.replicate addedNodes generation
                                            queued
                                            equalityQueued
                                            instances := instanceKey :: state.instances
                                            instanceHistory := state.instanceHistory.push
                                              { programVersion := state.programVersion + 1
                                                origin := retained.action
                                                family := request.key
                                                substitution := request.triggers
                                                products := resolved
                                                newNodes := generated
                                                generation
                                                equalities
                                                payload := request.payload }
                                            equalities := allEqualities
                                            metrics :=
                                              { state.metrics with
                                                admittedInstances :=
                                                  state.metrics.admittedInstances + 1
                                                generatedNodes :=
                                                  state.metrics.generatedNodes + addedNodes
                                                generatedEqualities :=
                                                  state.metrics.generatedEqualities +
                                                    equalities.length } }
                                        match enqueueNewEqualities state.equalities.size
                                            equalities.length prospective with
                                        | .error resource => .resourceLimit resource state
                                        | .ok prospective =>
                                            match enqueueNewApplications state.applications.size
                                                addedApplications prospective with
                                            | .error resource => .resourceLimit resource state
                                            | .ok next => .admitted generated next

/-- Select only an engine-retained proposal; callers cannot fabricate rule
provenance or transplant a proposal from another state. -/
def admitInstantiation (state : Engine Fact)
    (suggestion : SuggestionId) : AdmissionResult Fact :=
  match state.suggestions[suggestion.index]? with
  | none => .invalid .missingSuggestion state
  | some retained => admitRetained state retained

end Engine

end Hex.Interval.Experiment.Propagator
