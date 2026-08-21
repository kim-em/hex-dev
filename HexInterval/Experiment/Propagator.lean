/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.State
public import HexInterval.Experiment.StructuralCursor

@[expose] public section

/-!
# Function-agnostic propagation experiment

This module tests the request/reply boundary between an interval solver and
arbitrary function propagators.  The solver knows operation and rule keys, but
does not interpret either of them.  It owns only the expression DAG, current
facts, fact versions, dependency indexes, and deterministic resource counters.

A companion registry may keep caches of any Lean type.  It receives a
`RuleRequest` containing a bounded immutable structural view and exactly the
declared fact reads and writes, then replies with an `Outcome` bound to that
action.  Candidate facts are intersected by an engine-owned `FactDomain`;
function-specific code never enters the scheduler. Candidates remain
semantically untrusted: intersection can preserve consistency and monotonicity,
but only successful replay of their opaque proof payloads establishes
soundness.

The stable structural `Program`, `Fact`, and `Action` records live in the
supported Mathlib-free library. This module remains experimental because it
chooses concrete application storage, queues, resource counters, suggestion
handling, package callbacks, and search transitions. Selecting a retained
expression proposal runs a separate atomic validator before extending the live
program and appending its new concrete rule applications.
-/

namespace Hex.Interval.Experiment.Propagator

/-! # Experimental controller state -/

abbrev MatcherSize := StructuralCursor.Size
abbrev MatcherView := StructuralCursor.View
abbrev MatcherCursor := StructuralCursor.Cursor
abbrev MatcherLimits := StructuralCursor.Limits
abbrev MatcherError := StructuralCursor.Error
abbrev MatcherStep := StructuralCursor.Step StructuralInput

/-- A registration resolved against one concrete program node. -/
structure Application where
  rule : RuleId
  node : NodeId
  kind : ActionKind
  watches : List NodeId
  writes : List NodeId
  /-- Immutable registration baseline.  A retry prepares a new `Action` with
  an override; it never mutates this compiled application field. -/
  effort : Nat
  /-- Cached conservative semantic-surface charge for policy construction.
  It counts the validated ordered read and write projections even when one
  implementation can reuse part of that data without inspecting it again. -/
  policyItems : Nat := 0
  /-- Generation of the event which created this application.  Initial
  applications have generation zero. -/
  generation : Nat := 0
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

def opKeyExists (program : Program) (key : OpKey) : Bool :=
  program.operations.any fun operation => operation.key == key

/-- Resolve immutable scoped bindings in their declared order, followed by
every local `(registration, node)` match in node-major, registration-minor
order.  This layout makes local applications append-stable when new nodes are
instantiated.  Operation keys are opaque to this compiler. -/
def compileApplications (program : Program) (rules : Array Registration)
    (bindings : Array ScopeBinding := #[]) :
    Option (Array Application) := do
  if !program.check || !Registration.check program rules ||
      !ScopeBinding.checkAll program rules bindings then
    none
  else
    let mut applications := #[]
    let mut globalCompiled := Array.replicate rules.size false
    for binding in bindings do
      let (ruleId, rule) <- Registration.find? rules binding.rule
      applications := applications.push
        { rule := ruleId
          node := binding.anchor
          kind := rule.kind
          watches := binding.watches
          writes := binding.writes
          effort := rule.initialEffort
          policyItems := binding.watches.length + binding.writes.length }
    for nodeIndex in [0:program.nodes.size] do
      let node <- program.nodes[nodeIndex]?
      let operation <- program.operation? node.op
      for ruleIndex in [0:rules.size] do
        let rule <- rules[ruleIndex]?
        if rule.binding == .local && rule.head == operation.key then
          let watches <- Slot.resolveAll? { index := nodeIndex } node rule.watches
          let writes <- Slot.resolveAll? { index := nodeIndex } node rule.writes
          applications := applications.push
            { rule := { index := ruleIndex }
              node := { index := nodeIndex }
              kind := rule.kind
              watches
              writes
              effort := rule.initialEffort
              policyItems := watches.length + writes.length }
        else if rule.binding == .global && rule.head == operation.key &&
            !globalCompiled[ruleIndex]! then
          globalCompiled := globalCompiled.set! ruleIndex true
          applications := applications.push
            { rule := { index := ruleIndex }
              node := { index := nodeIndex }
              kind := rule.kind
              watches := []
              writes := []
              effort := rule.initialEffort }
    some applications

/-- Bounded application compiler.  Error `false` denotes an invalid program or
registry; error `true` denotes the exact application cap. -/
def compileApplicationsWithin (limit : Nat) (program : Program)
    (rules : Array Registration) (bindings : Array ScopeBinding := #[]) :
    Except Bool (Array Application) := do
  if !program.check || !Registration.check program rules ||
      !ScopeBinding.checkAll program rules bindings then
    throw false
  let mut applications := #[]
  let mut globalCompiled := Array.replicate rules.size false
  for binding in bindings do
    if limit <= applications.size then
      throw true
    let some (ruleId, rule) := Registration.find? rules binding.rule | throw false
    applications := applications.push
      { rule := ruleId
        node := binding.anchor
        kind := rule.kind
        watches := binding.watches
        writes := binding.writes
        effort := rule.initialEffort
        policyItems := binding.watches.length + binding.writes.length }
  for nodeIndex in [0:program.nodes.size] do
    let some node := program.nodes[nodeIndex]? | throw false
    let some operation := program.operation? node.op | throw false
    for ruleIndex in [0:rules.size] do
      let some rule := rules[ruleIndex]? | throw false
      if rule.binding == .local && rule.head == operation.key then
        if limit <= applications.size then
          throw true
        let some watches := Slot.resolveAll? { index := nodeIndex } node rule.watches
          | throw false
        let some writes := Slot.resolveAll? { index := nodeIndex } node rule.writes
          | throw false
        applications := applications.push
          { rule := { index := ruleIndex }
            node := { index := nodeIndex }
            kind := rule.kind
            watches
            writes
            effort := rule.initialEffort
            policyItems := watches.length + writes.length }
      else if rule.binding == .global && rule.head == operation.key &&
          !globalCompiled[ruleIndex]! then
        if limit <= applications.size then
          throw true
        globalCompiled := globalCompiled.set! ruleIndex true
        applications := applications.push
          { rule := { index := ruleIndex }
            node := { index := nodeIndex }
            kind := rule.kind
            watches := []
            writes := []
            effort := rule.initialEffort }
  pure applications

/-- Exact application identity used to validate append-only extension. -/
def Application.same (left right : Application) : Bool :=
  left.rule == right.rule && left.node == right.node && left.kind == right.kind &&
    left.watches == right.watches && left.writes == right.writes &&
      left.effort == right.effort && left.policyItems == right.policyItems &&
        left.generation == right.generation

/-- Scope-binding identity deliberately ignores creation generation so a later
proposal CSE-reuses an older identical application. -/
def Application.sameBinding (left right : Application) : Bool :=
  left.rule == right.rule && left.node == right.node && left.kind == right.kind &&
    left.watches == right.watches && left.writes == right.writes &&
      left.effort == right.effort && left.policyItems == right.policyItems

/-- Every old application, including its immutable baseline effort and
creation generation, must remain an exact prefix after program extension.
Retry escalation lives only in a selected `Action`, so it cannot invalidate
this structural prefix. -/
def applicationsPrefix (old new : Array Application) : Bool := Id.run do
  if new.size < old.size then return false
  for index in [0:old.size] do
    match old[index]?, new[index]? with
    | some left, some right => if !left.same right then return false
    | _, _ => return false
  return true

/-- Compile the application described by one already validated concrete
scope.  The registration snapshot, rather than proposal metadata, supplies
the action kind and baseline effort. -/
def applicationForBinding? (rules : Array Registration)
    (binding : ScopeBinding) : Option Application := do
  let (ruleId, rule) <- Registration.find? rules binding.rule
  if rule.binding != .scoped then none else pure ()
  pure
    { rule := ruleId
      node := binding.anchor
      kind := rule.kind
      watches := binding.watches
      writes := binding.writes
      effort := rule.initialEffort
      policyItems := binding.watches.length + binding.writes.length }

def findApplicationFrom (target : Application) : Nat -> List Application ->
    Option ApplicationId
  | _, [] => none
  | index, application :: applications =>
      if application.sameBinding target then some { index }
      else findApplicationFrom target (index + 1) applications

def findApplication? (applications : Array Application) (target : Application)
    (offset : Nat := 0) : Option ApplicationId :=
  findApplicationFrom target offset applications.toList

/-- Resolution of proposed scopes in proposal order.  `outputs` includes CSE
hits and repetitions; the other fields contain only new bindings and their
append-ready applications. -/
structure ScopeResolution where
  outputs : List ApplicationId
  freshBindings : List ScopeBinding
  freshApplications : Array Application
  deriving Repr

def resolveScopeApplicationsFrom (rules : Array Registration)
    (existing : Array Application) :
    List ApplicationId -> List ScopeBinding -> Array Application ->
      List ScopeBinding -> Option ScopeResolution
  | outputs, freshBindings, freshApplications, [] =>
      some { outputs, freshBindings, freshApplications }
  | outputs, freshBindings, freshApplications, binding :: bindings => do
      let application <- applicationForBinding? rules binding
      let existingId := findApplication? existing application
      let freshId :=
        findApplication? freshApplications application existing.size
      match existingId.orElse (fun _ => freshId) with
      | some identifier =>
          resolveScopeApplicationsFrom rules existing
            (outputs ++ [identifier]) freshBindings freshApplications bindings
      | none =>
          let identifier : ApplicationId :=
            { index := existing.size + freshApplications.size }
          resolveScopeApplicationsFrom rules existing
            (outputs ++ [identifier]) (freshBindings ++ [binding])
            (freshApplications.push application) bindings

def resolveScopeApplications (rules : Array Registration)
    (existing : Array Application) (bindings : List ScopeBinding) :
    Option ScopeResolution :=
  resolveScopeApplicationsFrom rules existing [] [] #[] bindings

/-- Compile local applications anchored only in an appended node suffix.
`limit` bounds the returned suffix, not the final application array. -/
def compileLocalApplicationsWithin (limit start : Nat) (program : Program)
    (rules : Array Registration) (existing : Array Application := #[])
    (generation : Nat := 0) :
    Except Bool (Array Application) := do
  if program.nodes.size < start || !program.check || !Registration.check program rules then
    throw false
  let mut applications := #[]
  let mut globalCompiled := Array.replicate rules.size false
  for application in existing do
    if application.rule.index < rules.size then
      globalCompiled := globalCompiled.set! application.rule.index true
    else
      throw false
  for nodeIndex in [start:program.nodes.size] do
    let some node := program.nodes[nodeIndex]? | throw false
    let some operation := program.operation? node.op | throw false
    for ruleIndex in [0:rules.size] do
      let some rule := rules[ruleIndex]? | throw false
      if rule.binding == .local && rule.head == operation.key then
        if limit <= applications.size then throw true
        let some watches := Slot.resolveAll? { index := nodeIndex } node rule.watches
          | throw false
        let some writes := Slot.resolveAll? { index := nodeIndex } node rule.writes
          | throw false
        applications := applications.push
          { rule := { index := ruleIndex }
            node := { index := nodeIndex }
            kind := rule.kind
            watches
            writes
            effort := rule.initialEffort
            policyItems := watches.length + writes.length
            generation }
      else if rule.binding == .global && rule.head == operation.key &&
          !globalCompiled[ruleIndex]! then
        if limit <= applications.size then throw true
        globalCompiled := globalCompiled.set! ruleIndex true
        applications := applications.push
          { rule := { index := ruleIndex }
            node := { index := nodeIndex }
            kind := rule.kind
            watches := []
            writes := []
            effort := rule.initialEffort
            generation }
  pure applications

/-! # Request/reply protocol -/

/-- Immutable proof-payload address allocated by the experimental companion
registry. It is not a pointer into mutable package cache state. -/
structure PayloadId where
  index : Nat
  deriving DecidableEq, Repr

/-- One semantically untrusted proposed fact. Its payload must later replay to
an independently checked theorem. -/
structure Candidate (Fact : Type) where
  node : NodeId
  fact : Fact
  payload : PayloadId

/-- A reference in one proposed expression extension. -/
inductive NodeRef where
  | existing (node : NodeId)
  | proposed (index : Nat)
  deriving DecidableEq, Repr

/-- One SSA instruction proposed by an experimental package matcher. -/
structure ProposedNode where
  domain : DomainId
  op : OpId
  args : List NodeRef
  deriving Repr

/-- One untrusted equality proposed alongside an extension. -/
structure ProposedEquality where
  left : NodeRef
  right : NodeRef
  payload : PayloadId
  deriving Repr

/-- One scoped application proposed against the atomically extended program. -/
structure ProposedScope where
  rule : RuleKey
  anchor : NodeRef
  watches : List NodeRef
  writes : List NodeRef
  deriving Repr

/-- Experimental atomic append-only expression-extension request. `key` is a
provisional package/policy family and is deliberately not part of the
supported action contract. -/
structure InstantiationRequest where
  key : Nat
  nodes : List ProposedNode
  equalities : List ProposedEquality
  scopes : List ProposedScope := []
  payload : PayloadId
  deriving Repr

/-- Why an experimental package recommends a proof-state split. -/
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

/-- An experimental split suggestion. A checked branch manager owns child
scopes and facts. -/
structure SplitRequest where
  node : NodeId
  point : Dyadic
  reason : SplitReason

/-- Cached policy-key surface for one validated instantiation proposal. -/
def instantiationPolicyItems (request : InstantiationRequest) : Nat :=
  request.nodes.length + request.equalities.length + request.scopes.length +
    request.nodes.foldl (fun count node => count + node.args.length) 0 +
    request.scopes.foldl (fun count scope =>
      count + 1 + scope.watches.length + scope.writes.length) 0

/-- Non-fact information returned to the search policy. -/
inductive Suggestion where
  | retry (effort : Nat)
  | instantiate (request : InstantiationRequest)
  | split (request : SplitRequest)

/-- Whether losing this suggestion can leave propagation unfinished. Splits
are optional proof search; retry and instantiation can expose further
contraction in the current branch. -/
def Suggestion.affectsClosure : Suggestion -> Bool
  | .retry _ | .instantiate _ => true
  | .split _ => false

/-- Why a bounded reply suggestion did not enter retained policy state. -/
inductive SuggestionDrop where
  | capacity (suggestion : Suggestion)
  | depth (suggestion : Suggestion)

namespace SuggestionDrop

def suggestion : SuggestionDrop -> Suggestion
  | .capacity suggestion | .depth suggestion => suggestion

def affectsClosure (drop : SuggestionDrop) : Bool :=
  drop.suggestion.affectsClosure

end SuggestionDrop

/-- Exact result of validating and capacity-filtering one reply's suggestions.
Both lists retain source order. Every dropped suggestion records whether
retained capacity or structural depth excluded it. -/
structure SuggestionPlan where
  kept : List Suggestion := []
  dropped : List SuggestionDrop := []

namespace SuggestionPlan

def capacityDrops (plan : SuggestionPlan) : Nat :=
  plan.dropped.foldl (fun count drop =>
    match drop with
    | .capacity _ => count + 1
    | .depth _ => count) 0

def depthDrops (plan : SuggestionPlan) : Nat :=
  plan.dropped.foldl (fun count drop =>
    match drop with
    | .capacity _ => count
    | .depth _ => count + 1) 0

def affectsClosure (plan : SuggestionPlan) : Bool :=
  plan.dropped.any SuggestionDrop.affectsClosure

end SuggestionPlan

/-- A policy candidate paired with engine-owned invocation provenance.  Split
proposals retain the target version at proposal time; later policy adoption
must not re-arm a guard from the then-current fact. -/
structure RetainedSuggestion where
  action : Action
  suggestion : Suggestion
  splitVersion : Option Nat
  /-- Cached semantic items inspected when policy constructs the suggestion
  key, including the source action's structural matcher inputs.  Reply
  validation derives this under the proposal and matcher-batch limits. -/
  policyItems : Nat := 0

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

def CostObservation.bounded (limit : Nat) (cost : CostObservation) : Bool :=
  cost.arithmeticWork <= limit && cost.visitedEntries <= limit &&
    cost.estimatedProofNodes <= limit

/-- A rule reply.  Only `success` may contain facts or structural suggestions;
the other cases are precise negative observations for policy and diagnostics. -/
inductive Outcome (Fact : Type) where
  | success (candidates : List (Candidate Fact))
      (suggestions : List Suggestion) (cost : CostObservation)
  | noChange (cost : CostObservation)
  | inapplicable
  | resourceLimit (budget : Nat)
  | failed (code : Nat)

/-- Bound performed-work observations separately from negative diagnostic
encodings.  A `resourceLimit` number is not charged as work, but it still needs
an independent representation cap before entering retained policy events. -/
def Outcome.observationBounded (costLimit diagnosticLimit : Nat) : Outcome Fact -> Bool
  | .success _ _ cost | .noChange cost => cost.bounded costLimit
  | .resourceLimit diagnostic | .failed diagnostic => diagnostic <= diagnosticLimit
  | .inapplicable => true

/-- Registry response bound to the exact outstanding invocation. -/
structure Reply (Fact : Type) where
  serial : Nat
  programVersion : Nat
  application : ApplicationId
  outcome : Outcome Fact

def _root_.Hex.Interval.Action.reply (action : Action) (outcome : Outcome Fact) : Reply Fact :=
  { serial := action.serial
    programVersion := action.programVersion
    application := action.application
    outcome }

/-- Bounded list check which inspects at most one constructor beyond the
trusted limit. -/
def listWithin {alpha : Type} : Nat -> List alpha -> Bool
  | _, [] => true
  | 0, _ :: _ => false
  | limit + 1, _ :: items => listWithin limit items

/-! # Experimental provenance and structural arenas -/

/-- Why one narrowed fact was admitted.  Rule provenance retains the proposed
fact separately from the narrowed fact installed in the event.  Equality
transport is an engine operation and therefore does not invent a registry rule
or payload. -/
inductive FactCause (Fact : Type) where
  | rule (action : Action) (proposed : Fact) (payload : PayloadId)
  | transport (equality : EqualityId) (source : SeenVersion)
  deriving Repr

/-- Canonical unordered endpoint pair for one generated equality. -/
structure EqualityPair where
  first : NodeId
  second : NodeId
  deriving DecidableEq, Repr

/-- Engine-derived structural identity for one shape-rule application in this
single-branch experiment.  A rule's untrusted family label is deliberately
absent: the originating rule, authoritative action substitution, resolved
products, and equality products determine whether the network changes. -/
structure InstanceKey where
  rule : RuleKey
  substitution : List NodeId
  structural : List StructuralKey := []
  products : List NodeId
  scopes : List ScopeBinding := []
  equalities : List EqualityPair
  deriving DecidableEq, Repr

/-- Structurally retained equality edge.  Its opaque payload is replay data;
the engine uses only its typed endpoints for untrusted search propagation. -/
structure EqualityEdge where
  left : NodeId
  right : NodeId
  generation : Nat
  origin : Action
  payload : PayloadId

def equalityPair (left right : NodeId) : EqualityPair :=
  if left.index <= right.index then { first := left, second := right }
  else { first := right, second := left }

def EqualityPair.before (left right : EqualityPair) : Bool :=
  left.first.index < right.first.index ||
    (left.first.index == right.first.index && left.second.index <= right.second.index)

def insertEqualityPair (pair : EqualityPair) : List EqualityPair -> List EqualityPair
  | [] => [pair]
  | next :: rest =>
      if pair.before next then pair :: next :: rest
      else next :: insertEqualityPair pair rest

/-- Replay-facing provenance for one committed program extension. -/
structure InstanceEvent where
  /-- Program snapshot after this extension commits. -/
  programVersion : Nat
  origin : Action
  family : Nat
  substitution : List NodeId
  products : List NodeId
  newNodes : List NodeId
  /-- Resolved scope bindings in proposal order, including repetitions. -/
  bindings : List ScopeBinding := []
  /-- The fresh binding subset appended by this event. -/
  newBindings : List ScopeBinding := []
  /-- Scoped application outputs in proposal order, including CSE hits. -/
  applications : List ApplicationId := []
  /-- The fresh application subset appended by this event. -/
  newApplications : List ApplicationId := []
  generation : Nat
  /-- Equality outputs in proposal order, including links reused from an older
  instance and repeated references to the same canonical link. -/
  equalities : List EqualityId
  /-- The fresh equality suffix appended by this event, in array order. -/
  newEqualities : List EqualityId := []
  payload : PayloadId

/-- Live state of the function-agnostic scheduler. Its branch facts,
dependency bits, append-only work queue, and chronology order are the supported
plain-data contracts; package callbacks and structural arenas remain here. -/
structure Engine (Fact : Type) extends
    Hex.Interval.State.Branch Fact (FactCause Fact), Hex.Interval.State.Dependencies, Hex.Interval.State.Queue,
      Hex.Interval.Trace.Order where
  /-- Eager runtime cache of the current facts. The supported branch keeps
  seeds and history authoritative; this experimental cache never becomes
  proof evidence. Engine transitions update both together. -/
  facts : Array Fact
  factDomain : FactDomain Fact
  rules : Array Registration
  /-- Concrete scoped bindings in admission order.  Start-time bindings form
  the initial prefix; dynamically proposed bindings append without moving any
  existing application identifier.  This is an audit log, not a recipe for
  recompiling `applications`: dynamic scopes and local applications interleave,
  and creation generations live in the canonical append-only arena below. -/
  bindings : Array ScopeBinding
  /-- Package/session-owned semantic preflight for a concrete scoped binding.
  The engine also performs all structural checks.  This veto protects package
  callback contracts; proof replay remains the soundness boundary. -/
  acceptsScope : Program -> ScopeBinding -> Bool := fun _ _ => true
  applications : Array Application
  /-- Engine-owned matcher progress, aligned exactly with `applications`.
  Ordinary applications carry `none`; matcher applications carry their
  append-stable cursor. -/
  matcherCursors : Array (Option MatcherCursor)
  pending : Option Action
  /-- Prepared matcher progress for the pending action.  This cursor never
  crosses the registry request boundary and commits only with a valid reply. -/
  pendingMatcher : Option MatcherCursor
  suggestions : Array RetainedSuggestion
  instances : List InstanceKey
  instanceHistory : Array InstanceEvent
  equalities : Array EqualityEdge
  metrics : Hex.Interval.State.Metrics
  limits : Hex.Interval.State.Limits

/-- Failure while validating and compiling an initial engine snapshot. -/
inductive StartError where
  | invalidProgram
  | invalidRegistrations
  | invalidBindings
  | wrongFactCount
  | resourceLimit (resource : Hex.Interval.State.Resource)
  deriving DecidableEq, Repr

/-- Build the dependency index in application order followed by equality order.
Each equality is one undirected contractor watching both endpoints. -/
def buildWatchers (nodeCount : Nat) (applications : Array Application)
    (equalities : Array EqualityEdge) : Option (Array (List Hex.Interval.State.Work)) := do
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

/-- Freeze the three append-only structural arena sizes without copying their
contents. -/
def matcherViewOf (programVersion nodeCount equalityCount applicationCount : Nat) :
    MatcherView :=
  { programVersion
    size :=
      { nodes := nodeCount
        equalities := equalityCount
        applications := applicationCount } }

/-- Allocate engine-owned cursors for one application suffix.  A newly created
matcher scans the complete current network; existing matcher cursors are never
reset by this helper. -/
def matcherCursorSuffix? (rules : Array Registration)
    (applications : Array Application) (start : Nat) (view : MatcherView) :
    Option (Array (Option MatcherCursor)) := do
  if applications.size < start then none else pure ()
  let mut cursors := #[]
  for index in [start:applications.size] do
    let application <- applications[index]?
    let rule <- rules[application.rule.index]?
    cursors := cursors.push <|
      if rule.matchWatch == .network then
        some (StructuralCursor.Cursor.start view)
      else
        none
  pure cursors

/-- Resource-first validation shared by checked frontends and `Engine.start`.
Size caps precede every traversal of untrusted program or registry metadata. -/
def preflightStart (program : Program) (rules : Array Registration)
    (factCount : Nat) (limits : Hex.Interval.State.Limits) (bindings : Array ScopeBinding := #[]) :
    Except StartError Unit := do
  if limits.maxOperations < program.operations.size then
    throw (.resourceLimit .operations)
  if limits.maxNodes < program.nodes.size then
    throw (.resourceLimit .nodes)
  if limits.maxRules < rules.size then
    throw (.resourceLimit .rules)
  if limits.maxApplications < bindings.size then
    throw (.resourceLimit .applications)
  if rules.any (fun rule => limits.maxEffort < rule.initialEffort) then
    throw (.resourceLimit .effort)
  if program.operations.any (fun operation => !listWithin limits.maxArity operation.inputs) ||
      program.nodes.any (fun node => !listWithin limits.maxArity node.args) ||
      rules.any (fun rule => !listWithin (limits.maxArity + 1) rule.watches ||
        !listWithin (limits.maxArity + 1) rule.writes) then
    throw (.resourceLimit .arity)
  if bindings.any (fun binding => !listWithin limits.maxScopeNodes binding.watches ||
      !listWithin limits.maxScopeNodes binding.writes) then
    throw (.resourceLimit .scopes)
  if factCount != program.nodes.size then
    throw .wrongFactCount
  if !program.check then
    throw .invalidProgram
  let some depths := program.depths? | throw .invalidProgram
  if depths.any (fun depth => limits.maxNodeDepth < depth) then
    throw (.resourceLimit .nodeDepth)
  if !Registration.check program rules then
    throw .invalidRegistrations
  if limits.matcherBatchSize == 0 &&
      rules.any (fun rule => rule.matchWatch == .network) then
    throw .invalidRegistrations
  if !ScopeBinding.checkAll program rules bindings then
    throw .invalidBindings

/-- Validate and compile an engine.  The caller supplies one initial fact per
node, ordinarily the domain top refined by source hypotheses. -/
def Engine.start (factDomain : FactDomain Fact) (program : Program) (rules : Array Registration)
    (facts : Array Fact) (limits : Hex.Interval.State.Limits) (bindings : Array ScopeBinding := #[])
    (acceptsScope : Program -> ScopeBinding -> Bool := fun _ _ => true) :
    Except StartError (Engine Fact) := do
  preflightStart program rules facts.size limits bindings
  if !bindings.all (acceptsScope program) then
    throw .invalidBindings
  let branch : Hex.Interval.State.Branch Fact (FactCause Fact) <-
    match Hex.Interval.State.Branch.startWithin limits program facts with
    | .ok branch => pure branch
    | .error .wrongFactCount => throw .wrongFactCount
    | .error (.resource resource) => throw (.resourceLimit resource)
    | .error _ => throw .invalidProgram
  let applications <-
    match compileApplicationsWithin limits.maxApplications program rules bindings with
    | .ok applications => pure applications
    | .error false => throw .invalidRegistrations
    | .error true => throw (.resourceLimit .applications)
  if limits.maxQueueEntries < applications.size then
    throw (.resourceLimit .queueEntries)
  let some watchers := buildWatchers program.nodes.size applications #[]
    | throw .invalidRegistrations
  let matcherView :=
    matcherViewOf 0 program.nodes.size 0 applications.size
  let some matcherCursors := matcherCursorSuffix? rules applications 0 matcherView
    | throw .invalidRegistrations
  let dependencies : Hex.Interval.State.Dependencies :=
    { watchers
      queued := Array.replicate applications.size true
      equalityQueued := #[] }
  let queue <-
    match Hex.Interval.State.Queue.initialWithin limits.maxQueueEntries applications.size with
    | .ok queue => pure queue
    | .error resource => throw (.resourceLimit resource)
  if !dependencies.check program.nodes.size applications.size 0 ||
      !queue.check dependencies program.nodes.size applications.size 0 limits.maxQueueEntries then
    throw .invalidRegistrations
  pure
    { toBranch := branch
      toDependencies := dependencies
      toQueue := queue
      toOrder := Hex.Interval.Trace.Order.empty
      facts
      factDomain
      rules
      bindings
      acceptsScope
      applications
      matcherCursors
      pending := none
      pendingMatcher := none
      suggestions := #[]
      instances := []
      instanceHistory := #[]
      equalities := #[]
      metrics := { queueInsertions := applications.size }
      limits }

/-! # Incremental scheduling -/

namespace Engine

/-- Freeze the current bounded expression structure for one registry request. -/
def programView (state : Engine Fact) : ProgramView :=
  { programVersion := state.programVersion
    operations := state.program.operations
    nodes := state.program.nodes
    generations := state.generations
    depths := state.depths }

/-- Constant-size structural view used to renew matcher cursors. -/
def matcherView (state : Engine Fact) : MatcherView :=
  matcherViewOf state.programVersion state.generations.size
    state.equalities.size state.applications.size

/-- Read one engine-owned creation generation by stable structural identifier. -/
def structuralGeneration? (state : Engine Fact) : StructuralKey -> Option Nat
  | .node node => state.generations[node.index]?
  | .equality equality =>
      state.equalities[equality.index]?.map (fun edge => edge.generation)
  | .application application =>
      state.applications[application.index]?.map (fun entry => entry.generation)

/-- Resolve one offset in a cursor's frozen canonical delta stream. -/
def matcherInputAt? (state : Engine Fact) (cursor : MatcherCursor)
    (offset : Nat) : Option StructuralInput := do
  let nodeCount := cursor.limit.nodes - cursor.base.nodes
  if offset < nodeCount then
    let key := StructuralKey.node { index := cursor.base.nodes + offset }
    let generation <- state.structuralGeneration? key
    return { key, generation }
  let offset := offset - nodeCount
  let equalityCount := cursor.limit.equalities - cursor.base.equalities
  if offset < equalityCount then
    let key := StructuralKey.equality { index := cursor.base.equalities + offset }
    let generation <- state.structuralGeneration? key
    return { key, generation }
  let offset := offset - equalityCount
  let applicationCount := cursor.limit.applications - cursor.base.applications
  if offset < applicationCount then
    let key := StructuralKey.application { index := cursor.base.applications + offset }
    let generation <- state.structuralGeneration? key
    return { key, generation }
  none

/-- Preview one matcher batch without advancing engine-owned progress.  An
exhausted old epoch is renewed over exactly the current append-only delta. -/
def previewMatcher (state : Engine Fact) (cursor : MatcherCursor) : MatcherStep :=
  if state.limits.maxMatcherVisits < state.metrics.matcherVisits then
    .invalidCursor
  else
    let view := state.matcherView
    let cursor? :=
      if cursor.exhausted then
        match StructuralCursor.renew view cursor with
        | .ok renewed => some renewed
        | .error _ => none
      else
        some cursor
    match cursor? with
    | none => .invalidCursor
    | some cursor =>
        let remaining :=
          state.limits.maxMatcherVisits - state.metrics.matcherVisits
        let limits : MatcherLimits :=
          { maxVisits := cursor.visits + remaining
            batchSize := state.limits.matcherBatchSize }
        StructuralCursor.take (state.matcherInputAt?) limits view cursor

/-- Shared matcher preparation used by both the FIFO and policy schedulers.
The prepared cursor remains engine-private. -/
inductive PreparedMatch where
  | ordinary
  | batch (inputs : List StructuralInput) (epoch : Nat) (next : MatcherCursor)
  | resourceLimit
  | invalid
  deriving Repr

def prepareMatch (state : Engine Fact) (application : ApplicationId)
    (rule : Registration) : PreparedMatch :=
  match rule.matchWatch, state.matcherCursors[application.index]? with
  | .none, some none => .ordinary
  | .network, some (some cursor) =>
      match state.previewMatcher cursor with
      | .yielded inputs next => .batch inputs.toList next.epoch next
      | .resourceLimit _ => .resourceLimit
      | .exhausted _ | .invalidCursor => .invalid
  | _, _ => .invalid

/-- Verify that every structural input still names the immutable generation
observed by the engine when it issued the matcher batch. -/
def structuralInputsFresh (state : Engine Fact) (inputs : List StructuralInput) : Bool :=
  inputs.all fun input => state.structuralGeneration? input.key == some input.generation

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

/-- An invocation remains usable across an append-only program extension only
when its concrete application, registration, and every watched fact version
still agree with the engine-owned provenance captured in the action. -/
def actionFresh (state : Engine Fact) (action : Action) : Bool :=
  match state.applications[action.application.index]?,
      state.rules[action.rule.index]?,
      state.seenVersions? (action.inputs.map fun input => input.node) with
  | some application, some rule, some current =>
      application.rule == action.rule && application.node == action.node &&
        application.kind == action.kind && application.generation == action.generation &&
        rule.key == action.key &&
        action.writes == application.writes &&
        (!rule.watchesProgram || action.programVersion == state.programVersion) &&
        action.inputs.map (fun input => input.node) == application.watches &&
        current == action.inputs &&
        state.structuralInputsFresh action.structuralInputs &&
        match rule.matchWatch, action.matcherEpoch with
        | .none, none => action.structuralInputs.isEmpty
        | .network, some _ => !action.structuralInputs.isEmpty
        | _, _ => false
  | _, _, _ => false

/-- Insert work unless it is already dirty.  The queue is an append-only work
log in this experiment, so its trusted cap also bounds total dependency churn. -/
def enqueue (state : Engine Fact) (work : Hex.Interval.State.Work) : Except Hex.Interval.State.Resource (Engine Fact) := do
  let suppressed := (Hex.Interval.State.Queue.dirty? state.toDependencies work).getD false
  let (dependencies, queue) <-
    match state.toQueue.enqueueWithin state.limits.maxQueueEntries
        state.program.nodes.size state.applications.size state.equalities.size
          state.toDependencies work with
    | .ok result => pure result
    | .error (.resource resource) => throw resource
    | .error .malformed =>
        throw <| match work with
          | .application _ => .applications
          | .equality _ => .equalities
  pure
    { state with
      toDependencies := dependencies
      toQueue := queue
      metrics :=
        if suppressed then
          { state.metrics with
            suppressedInsertions := state.metrics.suppressedInsertions + 1 }
        else
          { state.metrics with
            queueInsertions := state.metrics.queueInsertions + 1 } }

/-- Wake precisely the applications registered on one changed node. -/
def wakeNode (state : Engine Fact) (node : NodeId) :
    Except Hex.Interval.State.Resource (Engine Fact) := do
  let some applications := state.watchers[node.index]?
    | throw .nodes
  applications.foldlM enqueue state

/-- Wake the union of dependencies after every fact in one outcome has been
installed.  Queue suppression ensures that a multi-output contractor creates
at most one pending call per affected application. -/
def wakeNodes (state : Engine Fact) (nodes : List NodeId) :
    Except Hex.Interval.State.Resource (Engine Fact) :=
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
  | resourceLimit (resource : Hex.Interval.State.Resource) (state : Engine Fact)
  | invalidState (state : Engine Fact)

namespace Engine

/-- Issue one already prepared application request.  Matcher progress remains
only in the pending action until `submit` accepts a valid reply. -/
def issueApplication (state : Engine Fact) (applicationId : ApplicationId)
    (application : Application) (rule : Registration)
    (inputs : List SeenVersion) (views : List (FactView Fact))
    (structuralInputs : List StructuralInput := [])
    (matcherEpoch : Option Nat := none)
    (matcherNext : Option MatcherCursor := none) : Poll Fact :=
  let action : Action :=
    { serial := state.metrics.requests
      programVersion := state.programVersion
      application := applicationId
      rule := application.rule
      key := rule.key
      node := application.node
      kind := application.kind
      effort := application.effort
      generation := application.generation
      inputs
      writes := application.writes
      structuralInputs
      matcherEpoch }
  let next : Engine Fact :=
    { state with
      pending := some action
      pendingMatcher := matcherNext
      metrics :=
        { state.metrics with
          requests := state.metrics.requests + 1 } }
  .request
    { action
      program := state.programView
      inputs := views
      writes := application.writes }
    next

/-- Pop the next dirty work item.  Rule work freezes watched versions in an
action; equality work remains wholly inside the engine. -/
def poll (state : Engine Fact) : Poll Fact :=
  if state.pending.isSome then
    .awaitingReply state
  else if state.contradictory then
    .contradiction state
  else
    match state.toQueue.pop state.limits.maxQueueEntries state.program.nodes.size
        state.applications.size state.equalities.size state.toDependencies with
    | .error _ => .invalidState state
    | .ok (none, dependencies, queue) =>
        .saturated { state with toDependencies := dependencies, toQueue := queue }
    | .ok (some work, dependencies, queue) =>
        if state.limits.maxActions <= state.metrics.queuePops then
          .resourceLimit .actions state
        else
          let popped : Engine Fact :=
            { state with
              toDependencies := dependencies
              toQueue := queue
              metrics := { state.metrics with queuePops := state.metrics.queuePops + 1 } }
          match work with
          | .equality equalityId =>
              match state.equalities[equalityId.index]? with
              | some _ =>
                  .equality equalityId
                    { popped with
                      metrics :=
                        { popped.metrics with
                          equalityRuns := popped.metrics.equalityRuns + 1 } }
              | none => .invalidState state
          | .application applicationId =>
              match state.applications[applicationId.index]? with
              | some application =>
                  match state.rules[application.rule.index]?,
                      state.seenVersions? application.watches,
                      state.factViews? application.watches with
                  | some rule, some inputs, some views =>
                      match state.prepareMatch applicationId rule with
                      | .ordinary =>
                          issueApplication popped applicationId application rule inputs views
                      | .batch structuralInputs epoch next =>
                          issueApplication popped applicationId application rule inputs views
                            structuralInputs (some epoch) (some next)
                      | .resourceLimit => .resourceLimit .matcherVisits state
                      | .invalid => .invalidState state
                  | _, _, _ => .invalidState state
              | none => .invalidState state

end Engine

/-! # Atomic outcome admission -/

/-- Invalid registry reply.  These failures identify a broken registration or
an untrusted malformed outcome; none can establish a theorem. -/
inductive ReplyError where
  | noPendingAction
  | mismatchedAction
  | tooManyCandidates
  | tooManySuggestions
  | oversizedProposal
  | oversizedEffort
  | oversizedObservation
  | duplicateWrite
  | undeclaredWrite (node : NodeId)
  | missingFact (node : NodeId)
  | malformedProposal
  | malformedFact (code : Nat)
  deriving DecidableEq, Repr

/-- Result of atomically admitting one reply. -/
inductive ReplyResult (Fact : Type) where
  | accepted (plan : SuggestionPlan) (state : Engine Fact)
  | invalid (error : ReplyError) (state : Engine Fact)
  | resourceLimit (resource : Hex.Interval.State.Resource) (state : Engine Fact)
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

/-- Structural or fact-domain failure of an equality contraction. -/
inductive EqualityFault where
  | pendingReply
  | missingEquality
  | domainMismatch
  | missingState
  | oversizedDiagnostic
  | malformedFact (code : Nat)
  deriving DecidableEq, Repr

/-- Equality contractors are internal, atomic scheduler transitions. -/
inductive EqualityResult (Fact : Type) where
  | advanced (narrowCalls : Nat) (state : Engine Fact)
  | invalid (fault : EqualityFault) (narrowCalls : Nat) (state : Engine Fact)
  | resourceLimit (resource : Hex.Interval.State.Resource) (narrowCalls : Nat) (state : Engine Fact)
  | factResourceLimit (budget : Nat) (narrowCalls : Nat) (state : Engine Fact)

def existingRefBounded (nodeCount : Nat) : NodeRef -> Bool
  | .existing node => node.index < nodeCount
  | .proposed _ => true

def proposalBounded (nodeCount itemLimit scopeLimit : Nat)
    (request : InstantiationRequest) : Bool :=
  listWithin itemLimit request.nodes && listWithin itemLimit request.equalities &&
    listWithin itemLimit request.scopes &&
    request.nodes.all (fun node => listWithin itemLimit node.args &&
      node.args.all (existingRefBounded nodeCount)) &&
    request.equalities.all (fun edge =>
      existingRefBounded nodeCount edge.left && existingRefBounded nodeCount edge.right) &&
    request.scopes.all (fun scope =>
      existingRefBounded nodeCount scope.anchor &&
        listWithin scopeLimit scope.watches && listWithin scopeLimit scope.writes &&
        scope.watches.all (existingRefBounded nodeCount) &&
        scope.writes.all (existingRefBounded nodeCount))

def suggestionBounded (limits : Hex.Interval.State.Limits) (nodeCount : Nat) : Suggestion -> Bool
  | .retry effort => effort <= limits.maxEffort
  | .split request =>
      request.node.index < nodeCount &&
        (EndpointCost.ofDyadic request.point).allowed limits.splitEndpointLimit
  | .instantiate request =>
      proposalBounded nodeCount limits.maxProposalItems limits.maxScopeNodes request

def suggestionsBounded (limits : Hex.Interval.State.Limits) (nodeCount : Nat)
    (suggestions : List Suggestion) : Bool :=
  suggestions.all (suggestionBounded limits nodeCount)

def suggestionEffortBounded (limit : Nat) : Suggestion -> Bool
  | .retry effort => effort <= limit
  | .instantiate _ | .split _ => true

def suggestionsEffortBounded (limit : Nat) (suggestions : List Suggestion) : Bool :=
  suggestions.all (suggestionEffortBounded limit)

/-! # Structural proposal validation -/

/-- Exact syntactic node equality used by the experiment's linear CSE table. -/
def sameNode (left right : Node) : Bool :=
  left.domain == right.domain && left.op == right.op && left.args == right.args

/-- Linear reference CSE lookup.  The experiment measures this against indexed
tables before selecting a production representation. -/
def findNodeFrom : Nat -> List Node -> Node -> Option NodeId
  | _, [], _ => none
  | index, node :: nodes, target =>
      if sameNode node target then some { index } else findNodeFrom (index + 1) nodes target

def findNode? (program : Program) (target : Node) : Option NodeId :=
  findNodeFrom 0 program.nodes.toList target

/-- Resolve a draft reference.  `existing` IDs are restricted to the immutable
pre-proposal boundary; generated references use prior draft positions. -/
def resolveRef? (baseSize : Nat) (resolved : List NodeId) : NodeRef -> Option NodeId
  | .existing node => if node.index < baseSize then some node else none
  | .proposed index => resolved[index]?

def resolveRefs? (baseSize : Nat) (resolved : List NodeId)
    (refs : List NodeRef) : Option (List NodeId) :=
  refs.mapM (resolveRef? baseSize resolved)

/-- Failure while resolving the structural part of an untrusted proposal. -/
inductive DraftFault where
  | badReferenceOrShape
  deriving DecidableEq, Repr

/-- Resolve draft nodes in order, validate each typed SSA instruction, and CSE
against both old nodes and earlier new nodes.  Fresh nodes receive
`1 + max(argument depths)` (nullaries have depth zero); a CSE hit preserves
the engine-owned depth already stored for that node. This resolver is
deliberately uncapped: callers first validate the complete untrusted shape,
then separately classify only freshly appended depths. -/
def resolveDrafts (baseSize : Nat) :
    Program -> Array Nat -> List NodeId -> List ProposedNode ->
      Except DraftFault (Program × Array Nat × List NodeId)
  | program, depths, resolved, [] => pure (program, depths, resolved)
  | program, depths, resolved, draft :: drafts => do
      let some args := resolveRefs? baseSize resolved draft.args
        | throw .badReferenceOrShape
      let candidate : Node := { domain := draft.domain, op := draft.op, args }
      if !Program.nodeCheck program program.nodes.size candidate then
        throw .badReferenceOrShape
      let some candidateDepth := Program.nodeDepth? depths args
        | throw .badReferenceOrShape
      match findNode? program candidate with
      | some id =>
          let some storedDepth := depths[id.index]? | throw .badReferenceOrShape
          if storedDepth != candidateDepth then throw .badReferenceOrShape
          resolveDrafts baseSize program depths (resolved ++ [id]) drafts
      | none =>
          let id : NodeId := { index := program.nodes.size }
          resolveDrafts baseSize
            { program with nodes := program.nodes.push candidate }
            (depths.push candidateDepth) (resolved ++ [id]) drafts

/-- Whether every freshly appended node respects the structural-depth cap.
Existing nodes were checked when their program snapshot was created and are
not reclassified as losses of the current proposal. -/
def appendedDepthsWithin (baseSize maxNodeDepth : Nat) (depths : Array Nat) : Bool :=
  (depths.toList.drop baseSize).all fun depth => depth <= maxNodeDepth

/-- Canonical endpoint set requested by an instantiation, before existing-edge
deduplication.  This makes repeat selection detect the same instance even
after its equality has entered the live edge table. -/
def resolveRequestedPairs (baseSize : Nat) (resolved : List NodeId) (program : Program) :
    List ProposedEquality -> Option (List EqualityPair)
  | [] => some []
  | proposal :: proposals => do
      let left <- resolveRef? baseSize resolved proposal.left
      let right <- resolveRef? baseSize resolved proposal.right
      let leftNode <- program.node? left
      let rightNode <- program.node? right
      if left == right || leftNode.domain != rightNode.domain then none else pure ()
      let rest <- resolveRequestedPairs baseSize resolved program proposals
      let pair := equalityPair left right
      some (if rest.contains pair then rest else insertEqualityPair pair rest)

/-- Resolve dynamic contractor scopes in proposal order against the final
program snapshot.  Repeated scopes remain repeated here; application CSE is a
separate engine-owned step analogous to equality-edge CSE. -/
def resolveRequestedScopes (baseSize : Nat) (resolved : List NodeId)
    (program : Program) (rules : Array Registration) :
    List ProposedScope -> Option (List ScopeBinding)
  | [] => some []
  | proposal :: proposals => do
      let anchor <- resolveRef? baseSize resolved proposal.anchor
      let watches <- resolveRefs? baseSize resolved proposal.watches
      let writes <- resolveRefs? baseSize resolved proposal.writes
      let binding : ScopeBinding := { rule := proposal.rule, anchor, watches, writes }
      if !ScopeBinding.check program rules binding then none else pure ()
      let rest <- resolveRequestedScopes baseSize resolved program rules proposals
      some (binding :: rest)

/-- Result of validating a proposal before it can enter retained policy state. -/
inductive ProposalCheck where
  | valid
  | malformed
  | tooDeep

/-- Perform the same shape, typed-reference, equality, and structural-depth
checks used by admission, without mutating the live engine. Structural
validation deliberately runs to completion before the depth classification:
a malformed proposal cannot disguise itself as a recoverable depth loss. -/
def checkInstantiationProposal (program : Program) (depths : Array Nat)
    (maxNodeDepth : Nat) (request : InstantiationRequest)
    (rules : Array Registration := #[])
    (bindings : Array ScopeBinding := #[])
    (acceptsScope : Program -> ScopeBinding -> Bool := fun _ _ => true) : ProposalCheck :=
  let baseSize := program.nodes.size
  match resolveDrafts baseSize program depths [] request.nodes with
  | .error .badReferenceOrShape => .malformed
  | .ok (program, depths, resolved) =>
      match resolveRequestedPairs baseSize resolved program request.equalities,
          resolveRequestedScopes baseSize resolved program rules request.scopes with
      | some _, some scopes =>
          if !bindings.all (acceptsScope program) ||
              !scopes.all (acceptsScope program) then .malformed
          else if !appendedDepthsWithin baseSize maxNodeDepth depths then .tooDeep
          else .valid
      | _, _ => .malformed

namespace Engine

/-- Clear the request/reply latch and charge the registry reply. -/
def finishReply (state : Engine Fact) : Engine Fact :=
  { state with
    pending := none
    pendingMatcher := none
    metrics := { state.metrics with replies := state.metrics.replies + 1 } }

/-- Commit engine-owned matcher progress after, and only after, a valid reply.
The charged visit count is the cursor delta, so replaying a retained retry does
not pay again for an already committed batch.  If the frozen epoch still has
unseen inputs, or became exhausted while the network grew past its frozen
limit, requeue the same global matcher through the ordinary bounded worklist. -/
def commitMatcher (state : Engine Fact) (action : Action)
    (matcherNext : Option MatcherCursor) :
    Except Hex.Interval.State.Resource (Engine Fact) := do
  match matcherNext with
  | none =>
      if action.structuralInputs.isEmpty && action.matcherEpoch.isNone then
        pure state
      else
        throw .matcherVisits
  | some next =>
      let some (some stored) := state.matcherCursors[action.application.index]?
        | throw .applications
      let view := state.matcherView
      let start <-
        if stored.exhausted then
          match StructuralCursor.renew view stored with
          | .ok renewed => pure renewed
          | .error _ => throw .matcherVisits
        else
          pure stored
      let some epoch := action.matcherEpoch | throw .matcherVisits
      if !start.validFor view || !next.validFor view ||
          epoch != start.epoch || next.epoch != start.epoch ||
          next.programVersion != start.programVersion ||
          next.base != start.base || next.limit != start.limit ||
          next.offset < start.offset || next.visits < start.visits then
        throw .matcherVisits
      let visits := next.visits - start.visits
      if next.offset - start.offset != visits ||
          (visits != 0 && visits != action.structuralInputs.length) then
        throw .matcherVisits
      if state.limits.maxMatcherVisits < state.metrics.matcherVisits + visits then
        throw .matcherVisits
      let state :=
        { state with
          matcherCursors :=
            state.matcherCursors.set! action.application.index (some next)
          metrics :=
            { state.metrics with
              matcherVisits := state.metrics.matcherVisits + visits } }
      let hasUnseen <-
        if next.exhausted then
          match StructuralCursor.renew view next with
          | .ok renewed => pure (!renewed.exhausted)
          | .error _ => throw .matcherVisits
        else
          pure true
      if hasUnseen then
        state.enqueue (.application action.application)
      else
        pure state

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

/-- Attach proposal-time guards before any candidates from the same reply can
change facts. -/
def retainSuggestion (state : Engine Fact) (action : Action)
    (suggestion : Suggestion) : RetainedSuggestion :=
  { action
    suggestion
    splitVersion := match suggestion with
      | .split request => state.versions[request.node.index]?
      | .retry _ | .instantiate _ => none
    policyItems := action.structuralInputs.length +
      match suggestion with
      | .instantiate request => instantiationPolicyItems request
      | .retry _ | .split _ => 0 }

def candidateNodesUnique (candidates : List (Candidate Fact)) : Bool :=
  uniqueList (candidates.map (fun candidate => candidate.node))

def candidatesAuthorized (writes : List NodeId) (candidates : List (Candidate Fact)) :
    Option ReplyError :=
  match candidates.find? (fun candidate => !(writes.contains candidate.node)) with
  | some candidate => some (.undeclaredWrite candidate.node)
  | none => none

def installImprovement (action : Action) (candidate : Candidate Fact)
    (fact : Fact) (contradiction : Bool) (state : Engine Fact) :
    Except (ReplyError × Option Nat × Option Hex.Interval.State.Resource) (Engine Fact) := do
  if state.limits.maxAcceptedFacts <= state.history.size then
    throw (.malformedFact 0, none, some .acceptedFacts)
  else
    let version := state.versions[candidate.node.index]! + 1
    let previous : SeenVersion :=
      { node := candidate.node, version := state.versions[candidate.node.index]! }
    let event : Hex.Interval.State.Update Fact (FactCause Fact) :=
      { programVersion := action.programVersion
        node := candidate.node
        previous
        fact
        version
        cause := .rule action candidate.fact candidate.payload }
    let branch <-
      match state.toBranch.pushWithin state.limits event contradiction with
      | .ok branch => pure branch
      | .error _ => throw (.malformedFact 0, none, none)
    let order <-
      match state.toOrder.appendFact
          { maxFacts := state.limits.maxAcceptedFacts
            maxInstances := state.limits.maxInstances }
          state.history.size with
      | .ok order => pure order
      | .error .facts => throw (.malformedFact 0, none, some .acceptedFacts)
      | .error _ => throw (.malformedFact 0, none, none)
    pure
      { state with
        toBranch := branch
        facts := state.facts.set! candidate.node.index fact
        toOrder := order
        metrics :=
          { state.metrics with
            improvements := state.metrics.improvements + 1
            contradictions :=
              state.metrics.contradictions + if contradiction then 1 else 0 } }

/-- Install candidates without waking dependencies.  On failure, the caller
discards the returned working state and keeps the reply-cleared base state. -/
def installCandidates (action : Action) :
    Engine Fact -> List (Candidate Fact) ->
      Except (ReplyError × Option Nat × Option Hex.Interval.State.Resource) (Engine Fact × List NodeId)
  | state, [] => pure (state, [])
  | state, candidate :: candidates => do
      let some current := state.facts[candidate.node.index]?
        | throw (.missingFact candidate.node, none, none)
      let some target := state.program.node? candidate.node
        | throw (.missingFact candidate.node, none, none)
      let next <-
        match state.factDomain.narrow target.domain current candidate.fact with
        | .noChange => pure state
        | .malformed code =>
            if code <= state.limits.maxDiagnosticValue then
              throw (.malformedFact code, none, none)
            else
              throw (.oversizedObservation, none, none)
        | .resourceLimit budget =>
            if budget <= state.limits.maxDiagnosticValue then
              throw (.malformedFact 0, some budget, none)
            else
              throw (.oversizedObservation, none, none)
        | .improved fact => installImprovement action candidate fact false state
        | .contradiction fact => installImprovement action candidate fact true state
      let (next, changed) <- installCandidates action next candidates
      let changed :=
        if next.versions[candidate.node.index]! == state.versions[candidate.node.index]! then
          changed
        else
          candidate.node :: changed
      pure (next, changed)

/-- Remaining capacity in the engine-owned retained-suggestion array. -/
def suggestionRoom (state : Engine Fact) : Nat :=
  state.limits.maxRetainedSuggestions - state.suggestions.size

/-- A malformed suggestion which had room to enter policy state invalidates
the whole reply. Depth-limited structural suggestions are instead recoverable
losses recorded in `SuggestionPlan.dropped`. -/
inductive SuggestionCheck where
  | ready (plan : SuggestionPlan)
  | malformed

/-- Classify the exact suggestions which `submit` can retain. An unaffordable
instantiation does not consume retained capacity, so later affordable advice
from the same atomic reply can survive. Once capacity is exhausted, the
remaining suffix is dropped without structural validation, preserving the
existing rule that only work selected for retention can invalidate a reply. -/
def classifySuggestions (state : Engine Fact) :
    Nat -> List Suggestion -> SuggestionCheck
  | _, [] => .ready {}
  | 0, suggestions =>
      .ready { dropped := suggestions.map SuggestionDrop.capacity }
  | room + 1, suggestion :: suggestions =>
      let checked :=
        match suggestion with
        | .retry _ | .split _ => ProposalCheck.valid
        | .instantiate request =>
            checkInstantiationProposal state.program state.depths
              state.limits.maxNodeDepth request state.rules state.bindings state.acceptsScope
      match checked with
      | .malformed => .malformed
      | .valid =>
          match classifySuggestions state room suggestions with
          | .malformed => .malformed
          | .ready plan => .ready { plan with kept := suggestion :: plan.kept }
      | .tooDeep =>
          match classifySuggestions state (room + 1) suggestions with
          | .malformed => .malformed
          | .ready plan =>
              .ready { plan with dropped := .depth suggestion :: plan.dropped }

/-- Apply the live retained-suggestion capacity to one already surface-bounded
reply. Engine admission and policy completeness accounting both use this exact
classification. -/
def suggestionPlan (state : Engine Fact)
    (suggestions : List Suggestion) : SuggestionCheck :=
  classifySuggestions state state.suggestionRoom suggestions

/-- Validate and atomically admit one rule reply.  Candidate facts are all
installed before the union of affected dependencies is woken. -/
def submit (state : Engine Fact) (reply : Reply Fact) : ReplyResult Fact :=
  match state.pending with
  | none => .invalid .noPendingAction state
  | some action =>
      let matcherNext := state.pendingMatcher
      if reply.serial != action.serial || reply.programVersion != action.programVersion ||
          reply.application != action.application then
        .invalid .mismatchedAction state
      else if !reply.outcome.observationBounded state.limits.maxObservationValue
          state.limits.maxDiagnosticValue then
        .invalid .oversizedObservation state.finishReply
      else
      match reply.outcome with
      | .noChange _ | .inapplicable | .resourceLimit _ | .failed _ =>
          let base := state.outcomeNegative reply.outcome
          match base.commitMatcher action matcherNext with
          | .ok next => .accepted {} next
          | .error resource => .resourceLimit resource base
      | .success candidates suggestions _ =>
          let base := state.finishReply
          if !listWithin state.limits.maxOutcomeCandidates candidates then
            .invalid .tooManyCandidates base
          else if !listWithin state.limits.maxOutcomeSuggestions suggestions then
            .invalid .tooManySuggestions base
          else if !suggestionsEffortBounded state.limits.maxEffort suggestions then
            .invalid .oversizedEffort base
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
                    match state.suggestionPlan suggestions with
                    | .malformed => .invalid .malformedProposal base
                    | .ready plan =>
                        let working : Engine Fact :=
                          { base with
                            suggestions := plan.kept.foldl
                              (fun retained suggestion => retained.push
                                (state.retainSuggestion action suggestion))
                              base.suggestions
                            metrics :=
                              { base.metrics with
                                candidates := base.metrics.candidates + candidates.length
                                droppedSuggestions :=
                                  base.metrics.droppedSuggestions + plan.dropped.length
                                capacityDrops :=
                                  base.metrics.capacityDrops + plan.capacityDrops
                                depthDrops :=
                                  base.metrics.depthDrops + plan.depthDrops } }
                        match installCandidates action working candidates with
                        | .error (_, some budget, _) =>
                            .factResourceLimit budget base
                        | .error (_, _, some resource) => .resourceLimit resource base
                        | .error (error, _, _) => .invalid error base
                        | .ok (working, changed) =>
                            match working.wakeNodes changed with
                            | .error resource => .resourceLimit resource base
                            | .ok next =>
                                match next.commitMatcher action matcherNext with
                                | .ok next => .accepted plan next
                                | .error resource => .resourceLimit resource base

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
    (state : Engine Fact) : Option (Engine Fact) := do
  let version := update.previous.version + 1
  let event : Hex.Interval.State.Update Fact (FactCause Fact) :=
    { programVersion := state.programVersion
      node := update.target
      previous := update.previous
      fact := update.fact
      version
      cause := .transport equality update.source }
  let branch <- (state.toBranch.pushWithin state.limits event update.contradiction).toOption
  let order <-
    (state.toOrder.appendFact
      { maxFacts := state.limits.maxAcceptedFacts
        maxInstances := state.limits.maxInstances }
      state.history.size).toOption
  pure
    { state with
      toBranch := branch
      facts := state.facts.set! update.target.index update.fact
      toOrder := order
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
  if state.pending.isSome then
    .invalid .pendingReply 0 state
  else match state.equalities[equalityId.index]? with
  | none => .invalid .missingEquality 0 state
  | some equality =>
      match state.program.node? equality.left, state.program.node? equality.right,
          state.facts[equality.left.index]?, state.facts[equality.right.index]?,
          state.versions[equality.left.index]?, state.versions[equality.right.index]? with
      | some leftNode, some rightNode, some leftFact, some rightFact,
          some leftVersion, some rightVersion =>
          if leftNode.domain != rightNode.domain then
            .invalid .domainMismatch 0 state
          else
            match transportUpdate equality.left equality.right leftVersion rightVersion
                (state.factDomain.narrow leftNode.domain leftFact rightFact) with
            | .error (.malformed code) =>
                if code <= state.limits.maxDiagnosticValue then
                  .invalid (.malformedFact code) 1 state
                else
                  .invalid .oversizedDiagnostic 1 state
            | .error (.resourceLimit budget) =>
                if budget <= state.limits.maxDiagnosticValue then
                  .factResourceLimit budget 1 state
                else
                  .invalid .oversizedDiagnostic 1 state
            | .ok left =>
                match transportUpdate equality.right equality.left rightVersion leftVersion
                    (state.factDomain.narrow leftNode.domain rightFact leftFact) with
                | .error (.malformed code) =>
                    if code <= state.limits.maxDiagnosticValue then
                      .invalid (.malformedFact code) 2 state
                    else
                      .invalid .oversizedDiagnostic 2 state
                | .error (.resourceLimit budget) =>
                    if budget <= state.limits.maxDiagnosticValue then
                      .factResourceLimit budget 2 state
                    else
                      .invalid .oversizedDiagnostic 2 state
                | .ok right =>
                    let updates := [left, right].filterMap id
                    if state.limits.maxAcceptedFacts < state.history.size + updates.length then
                      .resourceLimit .acceptedFacts 2 state
                    else
                      match updates.foldlM
                          (fun state update => installTransport equalityId update state) state with
                      | none => .invalid .missingState 2 state
                      | some working =>
                          let changed := updates.map fun update => update.target
                          match working.wakeNodes changed with
                          | .error resource => .resourceLimit resource 2 state
                          | .ok next => .advanced 2 next
      | _, _, _, _, _, _ => .invalid .missingState 0 state

end Engine

/-! # External registry driver -/

universe u

/-- Why a bounded request/reply run stopped. `saturated` means only that the
raw engine queue is empty: this driver neither selects retained suggestions
nor carries policy completeness, so it cannot certify a proof-search fixed
point. -/
inductive RunStop where
  | saturated
  | contradiction
  | engineResource (resource : Hex.Interval.State.Resource)
  | factResource (budget : Nat)
  | invalidReply (error : ReplyError)
  | invalidEngine
  | driverFuel
  deriving DecidableEq, Repr

/-- A run returns both solver state and the registry's arbitrary private cache.
The cache may itself existentially package `Type`-valued rule caches, so its
universe is independent of the engine's fact universe. -/
structure RunResult (Fact : Type) (Cache : Type u) where
  state : Engine Fact
  cache : Cache
  stop : RunStop

/-- Execute the request/reply protocol with a registry-owned cache.  `invoke`
is the only place where operation or rule keys acquire function-specific
meaning. -/
def drive {Cache : Type u}
    (invoke : Cache -> RuleRequest Fact -> Outcome Fact × Cache) :
    Nat -> Engine Fact -> Cache -> RunResult Fact Cache
  | 0, state, cache => { state, cache, stop := .driverFuel }
  | fuel + 1, state, cache =>
      match state.poll with
      | .request request awaiting =>
          let (outcome, cache) := invoke cache request
          match awaiting.submit (request.action.reply outcome) with
          | .accepted _ next => drive invoke fuel next cache
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
          | .advanced _ next => drive invoke fuel next cache
          | .invalid _ _ next => { state := next, cache, stop := .invalidEngine }
          | .resourceLimit resource _ next =>
              { state := next, cache, stop := .engineResource resource }
          | .factResourceLimit budget _ next =>
              { state := next, cache, stop := .factResource budget }
      | .awaitingReply state | .invalidState state =>
          { state, cache, stop := .invalidEngine }

/-! # Atomic expression instantiation -/

/-- Structural failure while validating a retained instantiation request. -/
inductive AdmissionError where
  | notInstantiation
  | pendingReply
  | missingSuggestion
  | staleSuggestion (proposed current : Nat)
  | oversizedProposal
  | badReferenceOrShape
  | invalidEquality
  | invalidScope
  | invalidCompiledProgram
  deriving DecidableEq, Repr

/-- Result of selecting one retained instantiation suggestion. -/
inductive AdmissionResult (Fact : Type) where
  | admitted (newNodes : List NodeId) (state : Engine Fact)
  | duplicate (state : Engine Fact)
  | invalid (error : AdmissionError) (state : Engine Fact)
  | resourceLimit (resource : Hex.Interval.State.Resource) (state : Engine Fact)

/-- Existing references named directly by one draft reference list. -/
def existingRefs (refs : List NodeRef) : List NodeId :=
  refs.foldr (fun ref nodes => match ref with
    | .existing node => node :: nodes
    | .proposed _ => nodes) []

def requestExistingRefs (request : InstantiationRequest) : List NodeId :=
  request.nodes.flatMap (fun node => existingRefs node.args) ++
    request.equalities.flatMap (fun edge => existingRefs [edge.left, edge.right]) ++
    request.scopes.flatMap (fun scope =>
      existingRefs (scope.anchor :: scope.watches ++ scope.writes))

/-- Canonical engine-owned substitution of an invocation: its anchor followed
by every declared fact dependency, with the first occurrence retained. -/
def actionSubstitution (action : Action) : List NodeId :=
  dedupList (action.node :: action.inputs.map (fun input => input.node))

/-- Recompute logical instantiation depth from the emitting application's
creation generation, the authoritative invocation, and every explicitly
existing node named by the proposal.  A proposed node remains an output of
this theorem instance when CSE reuses older storage, including when the output
is also an equality endpoint or scope port; storage order cannot manufacture a
proof dependency. -/
def inferredGeneration? (generations : Array Nat)
    (action : Action) (request : InstantiationRequest) : Option Nat := do
  let references := actionSubstitution action ++ requestExistingRefs request
  let mut greatest := action.generation
  for input in action.structuralInputs do
    greatest := Nat.max greatest input.generation
  for node in references do
    let generation <- generations[node.index]?
    greatest := Nat.max greatest generation
  some (greatest + 1)

/-- Recompute theorem-instantiation generation for a structurally validated
retained proposal.  Reply admission already checked the full draft shape, and
program-watching action freshness pins that validated snapshot.  Policy view
construction therefore rechecks only freshness and engine-owned provenance. -/
def Engine.instantiationGeneration? (state : Engine Fact)
    (retained : RetainedSuggestion) : Option Nat := do
  if !state.actionFresh retained.action then none else pure ()
  let .instantiate request := retained.suggestion | none
  inferredGeneration? state.generations retained.action request

/-- Treat equality endpoints as unordered for structural deduplication. -/
def EqualityEdge.sameEndpoints (edge : EqualityEdge) (left right : NodeId) : Bool :=
  (edge.left == left && edge.right == right) ||
    (edge.left == right && edge.right == left)

/-- Locate an already resolved equality in stable array/list order. -/
def findEqualityIdFrom (left right : NodeId) : Nat -> List EqualityEdge -> Option EqualityId
  | _, [] => none
  | index, edge :: edges =>
      if edge.sameEndpoints left right then some { index }
      else findEqualityIdFrom left right (index + 1) edges

/-- Resolve equality outputs in proposal order.  The identifier list includes
both reused and newly allocated links; `fresh` contains only edges that must be
appended to the live table. -/
def resolveEqualitiesFrom (baseSize generation : Nat) (origin : Action)
    (program : Program) (resolved : List NodeId) (existing : Array EqualityEdge) :
    List EqualityId -> List EqualityEdge -> List ProposedEquality ->
      Option (List EqualityId × List EqualityEdge)
  | identifiers, fresh, [] => some (identifiers, fresh)
  | identifiers, fresh, proposal :: proposals => do
      let left <- resolveRef? baseSize resolved proposal.left
      let right <- resolveRef? baseSize resolved proposal.right
      let leftNode <- program.node? left
      let rightNode <- program.node? right
      if left == right || leftNode.domain != rightNode.domain then
        none
      else
        let all := existing.toList ++ fresh
        match findEqualityIdFrom left right 0 all with
        | some identifier =>
            resolveEqualitiesFrom baseSize generation origin program resolved existing
              (identifiers ++ [identifier]) fresh proposals
        | none =>
            let identifier : EqualityId := { index := existing.size + fresh.length }
            let edge : EqualityEdge :=
              { left, right, generation, origin, payload := proposal.payload }
            resolveEqualitiesFrom baseSize generation origin program resolved existing
              (identifiers ++ [identifier]) (fresh ++ [edge]) proposals

def resolveEqualities (baseSize generation : Nat) (origin : Action) (program : Program)
    (resolved : List NodeId) (existing : Array EqualityEdge)
    (proposals : List ProposedEquality) : Option (List EqualityId × List EqualityEdge) :=
  resolveEqualitiesFrom baseSize generation origin program resolved existing [] [] proposals

def newNodeIds (baseSize totalSize : Nat) : List NodeId :=
  (List.range (totalSize - baseSize)).map fun offset => { index := baseSize + offset }

/-- Domain-correct top facts for a newly appended node suffix. -/
def newTopFacts (domain : FactDomain Fact) (baseSize : Nat)
    (nodes : Array Node) : Array Fact :=
  ((nodes.toList.drop baseSize).map fun node => domain.top node.domain).toArray

/-- Queue every newly compiled concrete application. -/
def enqueueNewApplications (oldCount newCount : Nat) (state : Engine Fact) :
    Except Hex.Interval.State.Resource (Engine Fact) :=
  (List.range newCount).foldlM
    (fun state offset => state.enqueue (.application { index := oldCount + offset })) state

/-- Existing applications which explicitly declared a dependency on the whole
program and are not already dirty.  Program extension is their versioned
wakeup source, analogous to a changed watched fact for ordinary rules. -/
def dormantProgramWatchers? (state : Engine Fact) : Option (List ApplicationId) := do
  let mut watchers := []
  for index in [0:state.applications.size] do
    let application <- state.applications[index]?
    let registration <- state.rules[application.rule.index]?
    let queued <- state.queued[index]?
    if registration.watchesProgram && !queued then
      watchers := { index } :: watchers
  pure watchers.reverse

def enqueueApplications (applications : List ApplicationId) (state : Engine Fact) :
    Except Hex.Interval.State.Resource (Engine Fact) :=
  applications.foldlM
    (fun state application => state.enqueue (.application application)) state

/-- Queue every newly admitted equality contractor. -/
def enqueueNewEqualities (oldCount newCount : Nat) (state : Engine Fact) :
    Except Hex.Interval.State.Resource (Engine Fact) :=
  (List.range newCount).foldlM
    (fun state offset => state.enqueue (.equality { index := oldCount + offset })) state

namespace Engine

/-- Record a structurally redundant proposal without creating a program
snapshot or consuming an instance slot. -/
def duplicateInstance (state : Engine Fact) : AdmissionResult Fact :=
  .duplicate
    { state with
      metrics :=
        { state.metrics with
          duplicateInstances := state.metrics.duplicateInstances + 1 } }

/-- Implementation transition for one retained shape proposal.  It remains
visible only because this experiment deliberately exposes the whole `Engine`
record for state-mutation benchmarks; production authority comes from an
abstract engine type, not from pretending this helper is an access boundary. -/
def admitRetained (state : Engine Fact)
    (retained : RetainedSuggestion) : AdmissionResult Fact :=
  if state.pending.isSome then
    .invalid .pendingReply state
  else
    match retained.suggestion with
    | .retry _ | .split _ => .invalid .notInstantiation state
    | .instantiate request =>
        if !proposalBounded state.program.nodes.size state.limits.maxProposalItems
            state.limits.maxScopeNodes request then
          .invalid .oversizedProposal state
        else if !state.actionFresh retained.action then
          .invalid (.staleSuggestion retained.action.programVersion state.programVersion) state
        else
          let baseSize := state.program.nodes.size
          match resolveDrafts baseSize state.program state.depths [] request.nodes with
          | .error .badReferenceOrShape => .invalid .badReferenceOrShape state
          | .ok (program, depths, resolved) =>
              let equalityPairs? :=
                resolveRequestedPairs baseSize resolved program request.equalities
              if equalityPairs?.isNone then
                .invalid .invalidEquality state
              else
                match resolveRequestedScopes baseSize resolved program state.rules
                    request.scopes with
                | none => .invalid .invalidScope state
                | some requestedScopes =>
                    if !state.bindings.all (state.acceptsScope program) ||
                        !requestedScopes.all (state.acceptsScope program) then
                      .invalid .invalidScope state
                    else if !appendedDepthsWithin baseSize state.limits.maxNodeDepth depths then
                      .resourceLimit .nodeDepth state
                    else
                      match resolveScopeApplications state.rules state.applications
                          requestedScopes with
                      | none => .invalid .invalidScope state
                      | some scopeResolution =>
                          let substitution := actionSubstitution retained.action
                          let instanceKey : InstanceKey :=
                            { rule := retained.action.key
                              substitution
                              structural :=
                                retained.action.structuralInputs.map (fun input => input.key)
                              products := resolved
                              scopes := requestedScopes
                              equalities := equalityPairs?.getD [] }
                          if state.instances.contains instanceKey then
                            duplicateInstance state
                          else
                            match inferredGeneration? state.generations retained.action request with
                            | none => .invalid .badReferenceOrShape state
                            | some generation =>
                                match resolveEqualities baseSize generation retained.action program
                                    resolved state.equalities request.equalities with
                                | none => .invalid .invalidEquality state
                                | some (equalityIds, equalities) =>
                                    let addedNodes := program.nodes.size - baseSize
                                    let addedScopes :=
                                      scopeResolution.freshApplications.size
                                    if addedNodes == 0 && equalities.isEmpty && addedScopes == 0 then
                                      duplicateInstance state
                                    else if state.limits.maxInstances <=
                                        state.instances.length then
                                      .resourceLimit .instances state
                                    else if state.limits.maxGeneration < generation then
                                      .resourceLimit .generation state
                                    else if state.limits.maxNodes < program.nodes.size then
                                      .resourceLimit .nodes state
                                    else if state.limits.maxEqualities <
                                        state.equalities.size + equalities.length then
                                      .resourceLimit .equalities state
                                    else if state.limits.maxApplications <
                                        state.applications.size + addedScopes then
                                      .resourceLimit .applications state
                                    else
                                      let room := state.limits.maxApplications -
                                        state.applications.size - addedScopes
                                      match compileLocalApplicationsWithin room baseSize program
                                          state.rules state.applications generation with
                                      | .error false =>
                                          .invalid .invalidCompiledProgram state
                                      | .error true => .resourceLimit .applications state
                                      | .ok localApplications =>
                                          let freshScopeApplications :=
                                            scopeResolution.freshApplications.map fun application =>
                                              { application with generation }
                                          let applications := state.applications ++
                                            freshScopeApplications ++ localApplications
                                          if !applicationsPrefix state.applications applications then
                                            .invalid .invalidCompiledProgram state
                                          else
                                            match dormantProgramWatchers? state with
                                            | none =>
                                                .invalid .invalidCompiledProgram state
                                            | some programWatchers =>
                                                let addedApplications := addedScopes +
                                                  localApplications.size
                                                if state.limits.maxQueueEntries <
                                                    state.queue.size + addedApplications +
                                                      equalities.length +
                                                        programWatchers.length then
                                                  .resourceLimit .queueEntries state
                                                else
                                                  let allEqualities := state.equalities ++
                                                    equalities.toArray
                                                  let matcherView :=
                                                    matcherViewOf (state.programVersion + 1)
                                                      program.nodes.size allEqualities.size
                                                      applications.size
                                                  match
                                                      buildWatchers program.nodes.size applications
                                                        allEqualities,
                                                      matcherCursorSuffix? state.rules applications
                                                        state.applications.size matcherView with
                                                  | none, _ | _, none =>
                                                      .invalid .invalidCompiledProgram state
                                                  | some watchers, some matcherSuffix =>
                                                      if state.matcherCursors.size !=
                                                          state.applications.size then
                                                        .invalid .invalidCompiledProgram state
                                                      else
                                                        let generated :=
                                                          newNodeIds baseSize program.nodes.size
                                                        let freshScopeIds : List ApplicationId :=
                                                          (List.range addedScopes).map fun offset =>
                                                            { index :=
                                                                state.applications.size + offset }
                                                        let freshEqualityIds : List EqualityId :=
                                                          (List.range equalities.length).map fun offset =>
                                                            { index :=
                                                                state.equalities.size + offset }
                                                        let queued := state.queued ++
                                                          Array.replicate addedApplications false
                                                        let equalityQueued := state.equalityQueued ++
                                                          Array.replicate equalities.length false
                                                        let freshFacts := newTopFacts
                                                          state.factDomain baseSize program.nodes
                                                        match state.toBranch.extendWithin state.limits
                                                            program freshFacts generation with
                                                        | .error _ =>
                                                            .invalid .invalidCompiledProgram state
                                                        | .ok branch =>
                                                          match state.toOrder.appendInstance
                                                              { maxFacts :=
                                                                  state.limits.maxAcceptedFacts
                                                                maxInstances :=
                                                                  state.limits.maxInstances }
                                                              state.instanceHistory.size with
                                                          | .error .instances =>
                                                              .resourceLimit .instances state
                                                          | .error _ =>
                                                              .invalid .invalidCompiledProgram state
                                                          | .ok order =>
                                                            let prospective : Engine Fact :=
                                                              { state with
                                                                toBranch := branch
                                                                facts := state.facts ++ freshFacts
                                                                bindings := state.bindings ++
                                                                  scopeResolution.freshBindings.toArray
                                                                applications
                                                                matcherCursors :=
                                                                  state.matcherCursors ++ matcherSuffix
                                                                watchers
                                                                queued
                                                                equalityQueued
                                                                instances :=
                                                                  instanceKey :: state.instances
                                                                instanceHistory :=
                                                                  state.instanceHistory.push
                                                                    { programVersion :=
                                                                        state.programVersion + 1
                                                                      origin := retained.action
                                                                      family := request.key
                                                                      substitution
                                                                      products := resolved
                                                                      newNodes := generated
                                                                      bindings := requestedScopes
                                                                      newBindings :=
                                                                        scopeResolution.freshBindings
                                                                      applications :=
                                                                        scopeResolution.outputs
                                                                      newApplications := freshScopeIds
                                                                      generation
                                                                      equalities := equalityIds
                                                                      newEqualities := freshEqualityIds
                                                                      payload := request.payload }
                                                                toOrder := order
                                                                equalities := allEqualities
                                                                metrics :=
                                                                  { state.metrics with
                                                                    admittedInstances :=
                                                                      state.metrics.admittedInstances + 1
                                                                    generatedNodes :=
                                                                      state.metrics.generatedNodes +
                                                                        addedNodes
                                                                    generatedScopes :=
                                                                      state.metrics.generatedScopes +
                                                                        addedScopes
                                                                    generatedEqualities :=
                                                                      state.metrics.generatedEqualities +
                                                                        equalities.length } }
                                                            if !prospective.toDependencies.check
                                                                program.nodes.size applications.size
                                                                  allEqualities.size ||
                                                                !prospective.toQueue.check
                                                                  prospective.toDependencies
                                                                  program.nodes.size applications.size
                                                                    allEqualities.size
                                                                    prospective.limits.maxQueueEntries then
                                                              .invalid .invalidCompiledProgram state
                                                            else match enqueueNewEqualities
                                                                state.equalities.size equalities.length
                                                                  prospective with
                                                            | .error resource =>
                                                                .resourceLimit resource state
                                                            | .ok prospective =>
                                                                match enqueueNewApplications
                                                                    state.applications.size
                                                                    addedApplications prospective with
                                                                | .error resource =>
                                                                    .resourceLimit resource state
                                                                | .ok prospective =>
                                                                    match enqueueApplications
                                                                        programWatchers prospective with
                                                                    | .error resource =>
                                                                        .resourceLimit resource state
                                                                    | .ok next =>
                                                                        .admitted generated next

/-- Select one proposal retained in this concrete engine snapshot.  This
experiment keeps `Engine` inspectable for benchmarks, so callers can still
forge a whole engine value by updating public fields; the production API must
hide that constructor rather than relying on opacity of this transition. -/
def admitInstantiation (state : Engine Fact)
    (suggestion : SuggestionId) : AdmissionResult Fact :=
  match state.suggestions[suggestion.index]? with
  | none => .invalid .missingSuggestion state
  | some retained => admitRetained state retained

end Engine

end Hex.Interval.Experiment.Propagator
