/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Executable
public import HexInterval.Policy

@[expose] public section

/-!
# Typed runtime events

This module is the supported Mathlib-free transition boundary between one
checked executable assembly and versioned branch state. Package callbacks
return typed raw events rather than proof objects. The engine authenticates
the exact application, ordered fact dependencies, write authority,
append-only program/binding/application suffixes, and an explicit equality
descriptor arena before committing the whole callback result.

Equality endpoints are exact in-program node identities, but the raw
descriptor is not a theorem that those nodes denote equal values. Transport is
only structural substitution through an admitted oriented descriptor: it has
no quote and copies the fact of an exact currently live source version to the
opposite endpoint. Semantic equality authority remains with later
package-schema replay.

The sealed `Applied` value is runtime provenance, not theorem evidence. It
contains enough exact data for a later Mathlib companion to quote fact,
equality, transport, and instance proof steps, whose package-owned schemas
must still be checked independently. Callback execution, arbitrary facts,
causes, and package measures remain non-preemptible.
-/

namespace Hex.Interval.Runtime

/-- One admitted structural equality. Compact identity is its exact array
position; endpoints, creation generation, and originating action are retained
instead of being inferred from a generation table. -/
structure Equality where
  left : NodeId
  right : NodeId
  generation : Nat
  origin : Action
  assumptions : List SeenVersion
  quote : Executable.Quote
  deriving DecidableEq, Repr

/-- A theorem-package fact proposal annotation paired with the exact installed
meet/update. `proposed` need not equal `update.fact`; a later package schema and
proof adapter must independently correlate or rederive the annotation from the
installed update. -/
structure FactStep (Fact Cause : Type) where
  action : Action
  update : State.Update Fact Cause
  proposed : Fact
  quote : Executable.Quote
  deriving DecidableEq

/-- A new equality at the next compact equality address. -/
structure EqualityStep where
  action : Action
  equality : EqualityId
  left : NodeId
  right : NodeId
  generation : Nat
  assumptions : List SeenVersion
  quote : Executable.Quote
  deriving DecidableEq, Repr

/-- An engine-owned structural fact transport across one previously admitted
equality. `source` must be the exact current version and its fact must equal the
installed update fact; transport carries no independent quotation. -/
structure TransportStep (Fact Cause : Type) where
  action : Action
  update : State.Update Fact Cause
  equality : EqualityId
  source : SeenVersion
  deriving DecidableEq

/-- One exact append-only program extension. The explicit suffix lists pin the
compact identities which a later proof quotation must reproduce. -/
structure InstanceStep (Fact : Type) where
  action : Action
  after : Program
  freshFacts : Array Fact
  bindings : Array ScopeBinding
  newNodes : List NodeId
  newBindings : List ScopeBinding
  newApplications : List ApplicationId
  generation : Nat
  quote : Executable.Quote
  deriving DecidableEq

/-- Ordered raw runtime chronology returned by one callback. -/
inductive Event (Fact Cause : Type)
  | fact (step : FactStep Fact Cause)
  | equality (step : EqualityStep)
  | transport (step : TransportStep Fact Cause)
  | instance (step : InstanceStep Fact)
  deriving DecidableEq

/-- One callback result. Contradiction is runtime status only and requires at
least one accepted fact or transport update. -/
structure Batch (Fact Cause : Type) where
  events : Array (Event Fact Cause)
  contradiction : Bool := false
  deriving DecidableEq

/-- Runtime-event limits. Package metadata/results/quotations and every
structural state dimension retain their independent executable/state caps. -/
structure Limits where
  executable : Executable.Limits
  maxEvents : Nat
  deriving DecidableEq, Repr

inductive Resource where
  | state (resource : Hex.Interval.State.Resource)
  | events
  | offers
  deriving DecidableEq, Repr

inductive Error where
  | executable (error : Executable.Error)
  | state (error : State.BranchError)
  | malformed
  | stale
  | unauthorized
  | wrongEquality
  | resource (resource : Resource)
  deriving DecidableEq, Repr

/-- Sealed exact equality table. It can grow only through `stepWithin`. -/
structure Arena where
  private mk ::
  items : Array Equality

/-- Sealed live runtime state. Assembly callbacks/caches, the branch, and the
equality arena therefore cannot be transplanted independently. The generation
base authenticates the inherited global assembly generation corresponding to
this branch's local program version zero. -/
structure State (Fact Cause : Type) where
  private mk ::
  assembly : Executable.Assembly Fact (Batch Fact Cause)
  branch : Hex.Interval.State.Branch Fact Cause
  arena : Arena
  generationBase : Nat
  serial : Nat
  instances : Nat

/-- Ordinary-import-sealed record of one accepted atomic callback result.
Every field is plain runtime data; theorem authority still belongs to later
schema replay. -/
structure Applied (Fact Cause : Type) where
  private mk ::
  before : Hex.Interval.State.Branch Fact Cause
  after : Hex.Interval.State.Branch Fact Cause
  beforeBindings : Array ScopeBinding
  afterBindings : Array ScopeBinding
  beforeApplications : Array Executable.Application
  afterApplications : Array Executable.Application
  beforeGeneration : Nat
  afterGeneration : Nat
  beforeEqualities : Array Equality
  afterEqualities : Array Equality
  action : Action
  events : Array (Event Fact Cause)
  quotes : Array Executable.Quote
  serial : Nat

/-- One runtime-owned offer-generation snapshot. The private constructor keeps
the exact live branch, executable tables, equality generations, chronology,
residual budgets, completeness, and generated actions inseparable. It is
scheduler data only: every selected action is still reauthenticated by
`stepWithin`. -/
structure OfferSnapshot (Fact Cause : Type) where
  private mk ::
  branch : Hex.Interval.State.Branch Fact Cause
  rules : Array Registration
  bindings : Array ScopeBinding
  applicationGenerations : Array Nat
  equalityGenerations : Array Nat
  /-- Common epoch of all matcher-owned applications. Mixed nonempty matcher
  epochs are rejected; zero is the canonical value when no row has an epoch. -/
  matcherEpoch : Nat
  serial : Nat
  remaining : Policy.EngineBudgetView
  /-- False only when every handler-approved runtime application can be
  represented by Search's scheduler contract. Repeated ordered read
  occurrences are representable; duplicate write or structural authority is
  not. A package handler's intentional `offers = false` veto does not make
  this incomplete. -/
  incomplete : Bool
  actions : Array Action

/-- One inseparable successful callback transition, its exact sticky-cache
runtime successor, and the completeness-marked offer snapshot generated from
that same successor. The private constructor prevents cache/state or
transition/snapshot transplants at the autonomous-controller boundary. -/
structure Advanced (Fact Cause : Type) where
  private mk ::
  transition : Applied Fact Cause
  state : State Fact Cause
  offers : OfferSnapshot Fact Cause

private def makeArena (items : Array Equality) : Arena := { items }

private def makeState (assembly : Executable.Assembly Fact (Batch Fact Cause))
    (branch : Hex.Interval.State.Branch Fact Cause) (arena : Arena)
    (generationBase serial instances : Nat) : State Fact Cause :=
  { assembly, branch, arena, generationBase, serial, instances }

private def makeApplied (before after : Hex.Interval.State.Branch Fact Cause)
    (beforeBindings afterBindings : Array ScopeBinding)
    (beforeApplications afterApplications : Array Executable.Application)
    (beforeGeneration afterGeneration : Nat)
    (beforeEqualities afterEqualities : Array Equality) (action : Action)
    (events : Array (Event Fact Cause)) (quotes : Array Executable.Quote)
    (serial : Nat) : Applied Fact Cause :=
  { before, after, beforeBindings, afterBindings, beforeApplications,
    afterApplications, beforeGeneration, afterGeneration, beforeEqualities,
    afterEqualities, action, events, quotes, serial }

variable {Fact Cause : Type}

def State.equalities (state : State Fact Cause) : Array Equality :=
  state.arena.items

private def listWithin {α : Type} : Nat → List α → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | limit + 1, _ :: rest => listWithin limit rest

private def fromBranch {α : Type} : Except State.BranchError α → Except Error α
  | .ok value => .ok value
  | .error error => .error (.state error)

private def preflightBranch (limits : State.Limits)
    (branch : Hex.Interval.State.Branch Fact Cause) : Except Error Unit := do
  if limits.maxOperations < branch.baseProgram.operations.size ||
      limits.maxOperations < branch.program.operations.size then
    throw (.resource (.state .operations))
  if limits.maxNodes < branch.baseProgram.nodes.size ||
      limits.maxNodes < branch.program.nodes.size ||
      limits.maxNodes < branch.initialFacts.size || limits.maxNodes < branch.seeds.size ||
      limits.maxNodes < branch.versions.size || limits.maxNodes < branch.generations.size ||
      limits.maxNodes < branch.depths.size then throw (.resource (.state .nodes))
  if limits.maxAcceptedFacts < branch.history.size then
    throw (.resource (.state .acceptedFacts))
  if branch.baseProgram.operations.any
      (fun operation => !listWithin limits.maxArity operation.inputs) ||
      branch.program.operations.any
        (fun operation => !listWithin limits.maxArity operation.inputs) ||
      branch.baseProgram.nodes.any (fun node => !listWithin limits.maxArity node.args) ||
      branch.program.nodes.any (fun node => !listWithin limits.maxArity node.args) then
    throw (.resource (.state .arity))
  pure ()

private def preflightAction (limits : State.Limits) (action : Action) :
    Except Error Unit := do
  if !listWithin (Nat.max (limits.maxArity + 1) limits.maxScopeNodes) action.inputs ||
      !listWithin (Nat.max (limits.maxArity + 1) limits.maxScopeNodes) action.writes then
    throw (.resource (.state .arity))
  if !listWithin limits.matcherBatchSize action.structuralInputs then
    throw (.resource (.state .matcherVisits))
  if limits.maxEffort < action.effort then throw (.resource (.state .effort))
  if limits.maxGeneration < action.generation then
    throw (.resource (.state .generation))

private def preflightEvent (limits : Limits) :
    Event Fact Cause → Except Error Unit
  | .fact step =>
      preflightAction limits.executable.state step.action
  | .transport step =>
      preflightAction limits.executable.state step.action
  | .equality step => do
      preflightAction limits.executable.state step.action
      if limits.executable.state.maxGeneration < step.generation then
        throw (.resource (.state .generation))
      if !listWithin (Nat.max (limits.executable.state.maxArity + 1)
          limits.executable.state.maxScopeNodes) step.assumptions then
        throw (.resource (.state .arity))
      pure ()
  | .instance step => do
      preflightAction limits.executable.state step.action
      if limits.executable.state.maxOperations < step.after.operations.size then
        throw (.resource (.state .operations))
      if limits.executable.state.maxNodes < step.after.nodes.size ||
          limits.executable.state.maxNodes < step.freshFacts.size ||
          !listWithin limits.executable.state.maxNodes step.newNodes then
        throw (.resource (.state .nodes))
      if step.after.operations.any (fun operation =>
          !listWithin limits.executable.state.maxArity operation.inputs) ||
          step.after.nodes.any (fun node =>
            !listWithin limits.executable.state.maxArity node.args) then
        throw (.resource (.state .arity))
      if limits.executable.state.maxApplications < step.bindings.size ||
          !listWithin limits.executable.state.maxApplications step.newBindings ||
          !listWithin limits.executable.state.maxApplications step.newApplications then
        throw (.resource (.state .applications))
      if step.bindings.any (fun binding =>
          !listWithin limits.executable.state.maxScopeNodes binding.watches ||
            !listWithin limits.executable.state.maxScopeNodes binding.writes) ||
          step.newBindings.any (fun binding =>
            !listWithin limits.executable.state.maxScopeNodes binding.watches ||
              !listWithin limits.executable.state.maxScopeNodes binding.writes) then
        throw (.resource (.state .scopes))
      if limits.executable.state.maxGeneration < step.generation then
        throw (.resource (.state .generation))
      pure ()

private def current (branch : Hex.Interval.State.Branch Fact Cause)
    (seen : SeenVersion) : Bool :=
  branch.versions[seen.node.index]? == some seen.version &&
    (branch.factAt? seen).isSome

private def inputsCurrent (branch : Hex.Interval.State.Branch Fact Cause)
    (inputs : List SeenVersion) : Bool :=
  inputs.all (current branch)

private def inputsAvailable (branch : Hex.Interval.State.Branch Fact Cause)
    (inputs : List SeenVersion) : Bool :=
  inputs.all fun seen => (branch.factAt? seen).isSome

private def expectedNodes (start count : Nat) : List NodeId :=
  (List.range count).map fun offset => { index := start + offset }

private def expectedApplications (start count : Nat) : List ApplicationId :=
  (List.range count).map fun offset => { index := start + offset }

private def suffix {α : Type} (before after : Array α) : List α :=
  (List.range (after.size - before.size)).filterMap fun offset =>
    after[before.size + offset]?

private def quoteOf : Event Fact Cause → Option Executable.Quote
  | .fact step => some step.quote
  | .equality step => some step.quote
  | .instance step => some step.quote
  | .transport _ => none

private def eventQuotes (events : Array (Event Fact Cause)) : Array Executable.Quote :=
  events.toList.filterMap quoteOf |>.toArray

private def inputViews (branch : Hex.Interval.State.Branch Fact Cause)
    (inputs : List SeenVersion) : Option (List (FactView Fact)) :=
  inputs.mapM fun seen => do
    let fact ← branch.factAt? seen
    pure { node := seen.node, fact, version := seen.version }

private def request? (limits : Limits) (state : State Fact Cause)
    (action : Action) : Option (RuleRequest Fact) := do
  if action.serial != state.serial || action.programVersion != state.branch.programVersion then
    none
  if !listWithin (Nat.max (limits.executable.state.maxArity + 1)
      limits.executable.state.maxScopeNodes) action.inputs ||
      !listWithin (Nat.max (limits.executable.state.maxArity + 1)
        limits.executable.state.maxScopeNodes) action.writes ||
      !listWithin limits.executable.state.matcherBatchSize action.structuralInputs then
    none
  let application ← state.assembly.applications[action.application.index]?
  if !application.accepts action.application action || !inputsCurrent state.branch action.inputs then
    none
  let inputs ← inputViews state.branch action.inputs
  pure
    { action
      program :=
        { programVersion := state.branch.programVersion
          operations := state.branch.program.operations
          nodes := state.branch.program.nodes
          generations := state.branch.generations
          depths := state.branch.depths }
      inputs
      writes := action.writes }

/-- Start from one exact version-zero branch and its already-assembled program.
Equality identity starts empty; importing a decoded equality arena is
deliberately unsupported. Application creation generations remain global to the
sealed assembly. The assembly generation at restart is authenticated as the
fixed base corresponding to branch-local program version zero; later strict
global generations are rebased onto consecutive local branch generations
without weakening either chronology. Callback serial and equality identity
also restart at zero. -/
opaque State.startWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (assembly : Executable.Assembly Fact (Batch Fact Cause))
    (branch : Hex.Interval.State.Branch Fact Cause) : Except Error (State Fact Cause) := do
  match assembly.preflightWithin limits.executable with
  | .error error => throw (.executable error)
  | .ok _ => pure ⟨⟩
  match preflightBranch limits.executable.state branch with
  | .error error => throw error
  | .ok _ => pure ⟨⟩
  if branch.programVersion != 0 || branch.program != assembly.program || !branch.check then
    throw .malformed
  pure (makeState assembly branch (makeArena #[]) assembly.generation 0 0)

private structure Cursor (Fact Cause : Type) where
  assembly : Executable.Assembly Fact (Batch Fact Cause)
  branch : Hex.Interval.State.Branch Fact Cause
  equalities : Array Equality
  generationBase : Nat
  instances : Nat

private def pushFact (limits : Limits) (cursor : Cursor Fact Cause)
    (action : Action) (step : FactStep Fact Cause) (contradiction : Bool) :
    Except Error (Cursor Fact Cause) :=
  if step.action != action || action.programVersion != cursor.branch.programVersion ||
      step.update.programVersion != cursor.branch.programVersion ||
      !action.writes.contains step.update.node || step.quote.role != .fact then
    .error .unauthorized
  else
    match fromBranch (Hex.Interval.State.Branch.pushWithin limits.executable.state
        cursor.branch step.update contradiction) with
    | .error error => .error error
    | .ok nextBranch => .ok
        { assembly := cursor.assembly
          branch := nextBranch
          equalities := cursor.equalities
          generationBase := cursor.generationBase
          instances := cursor.instances }

private def pushEquality (limits : Limits) (cursor : Cursor Fact Cause)
    (action : Action) (step : EqualityStep) : Except Error (Cursor Fact Cause) := do
  if limits.executable.state.maxEqualities <= cursor.equalities.size then
    throw (.resource (.state .equalities))
  if step.action != action || action.programVersion != cursor.branch.programVersion ||
      step.equality.index != cursor.equalities.size || step.left == step.right ||
      step.assumptions != action.inputs || !inputsAvailable cursor.branch step.assumptions ||
      step.generation != action.generation || step.quote.role != .equality then
    throw .wrongEquality
  let some left := cursor.branch.program.node? step.left | throw .wrongEquality
  let some right := cursor.branch.program.node? step.right | throw .wrongEquality
  if left.domain != right.domain then throw .wrongEquality
  let equality : Equality :=
    { left := step.left, right := step.right, generation := step.generation,
      origin := step.action, assumptions := step.assumptions, quote := step.quote }
  pure { cursor with equalities := cursor.equalities.push equality }

private def pushTransport [DecidableEq Fact] (limits : Limits) (cursor : Cursor Fact Cause)
    (action : Action) (step : TransportStep Fact Cause) (contradiction : Bool) :
    Except Error (Cursor Fact Cause) :=
  if step.action != action || action.programVersion != cursor.branch.programVersion ||
      step.update.programVersion != cursor.branch.programVersion ||
      !action.writes.contains step.update.node || !action.inputs.contains step.source ||
      !current cursor.branch step.source ||
      cursor.branch.factAt? step.source != some step.update.fact then .error .unauthorized
  else match cursor.equalities[step.equality.index]? with
    | none => .error .wrongEquality
    | some equality =>
      let oriented :=
        (step.update.node == equality.left && step.source.node == equality.right) ||
          (step.update.node == equality.right && step.source.node == equality.left)
      if !oriented then .error .wrongEquality
      else match fromBranch (Hex.Interval.State.Branch.pushWithin
          limits.executable.state cursor.branch step.update contradiction) with
        | .error error => .error error
        | .ok nextBranch => .ok
            { assembly := cursor.assembly
              branch := nextBranch
              equalities := cursor.equalities
              generationBase := cursor.generationBase
              instances := cursor.instances }

private def pushInstance (limits : Limits) (cursor : Cursor Fact Cause)
    (action : Action) (step : InstanceStep Fact) : Except Error (Cursor Fact Cause) :=
  if limits.executable.state.maxInstances <= cursor.instances then
    .error (.resource (.state .instances))
  else if step.action != action || action.kind != .instantiate ||
      action.programVersion != cursor.branch.programVersion || step.quote.role != .instance then
    .error .unauthorized
  else if step.generation != cursor.assembly.generation + 1 ||
      step.generation != cursor.generationBase + cursor.branch.programVersion + 1 then
    .error .malformed
  else if step.newNodes.isEmpty && step.newBindings.isEmpty &&
      step.newApplications.isEmpty then
    .error .malformed
  else if step.newNodes != expectedNodes cursor.branch.program.nodes.size
      (step.after.nodes.size - cursor.branch.program.nodes.size) ||
      step.newBindings != suffix cursor.assembly.bindings step.bindings then
    .error .malformed
  else match cursor.assembly.extendAllWithin limits.executable step.after
      step.bindings step.generation with
    | .error error => .error (.executable error)
    | .ok assembly =>
      let freshApplicationCount := assembly.applications.size - cursor.assembly.applications.size
      if step.newApplications != expectedApplications cursor.assembly.applications.size
          freshApplicationCount then .error .malformed
      else match fromBranch (Hex.Interval.State.Branch.extendWithin
          limits.executable.state cursor.branch step.after step.freshFacts
            (cursor.branch.programVersion + 1)) with
        | .error error => .error error
        | .ok nextBranch => .ok
            { assembly := assembly
              branch := nextBranch
              equalities := cursor.equalities
              generationBase := cursor.generationBase
              instances := cursor.instances + 1 }

private def preflightBatch (limits : Limits) (batch : Batch Fact Cause) :
    Except Error Unit := do
  if limits.maxEvents < batch.events.size then throw (.resource .events)
  if batch.events.isEmpty then throw .malformed
  for event in batch.events do
    match preflightEvent limits event with
    | .error error => throw error
    | .ok _ => pure ⟨⟩
  if batch.contradiction && !batch.events.any (fun
      | .fact _ | .transport _ => true
      | _ => false) then throw .malformed

private def applyEvents [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (state : State Fact Cause) (action : Action)
    (batch : Batch Fact Cause) : Except Error (Cursor Fact Cause) := do
  let mut cursor : Cursor Fact Cause :=
    { assembly := state.assembly, branch := state.branch,
      equalities := state.arena.items, generationBase := state.generationBase,
      instances := state.instances }
  for event in batch.events do
    cursor ← match event with
      | .fact step => pushFact limits cursor action step batch.contradiction
      | .equality step => pushEquality limits cursor action step
      | .transport step => pushTransport limits cursor action step batch.contradiction
      | .instance step => pushInstance limits cursor action step
  pure cursor

/-- Execute the exact assembled callback once and commit its whole typed raw
event batch transactionally. The callback result cannot partially update the
branch, equality arena, assembly cache, or compact application table. -/
opaque State.stepWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (state : State Fact Cause) (action : Action) :
    Except Error (Applied Fact Cause × State Fact Cause) := do
  if limits.executable.state.maxActions <= state.serial then
    throw (.resource (.state .actions))
  match preflightBranch limits.executable.state state.branch with
  | .error error => throw error
  | .ok _ => pure ⟨⟩
  if limits.executable.state.maxEqualities < state.arena.items.size then
    throw (.resource (.state .equalities))
  if limits.executable.state.maxInstances < state.instances then
    throw (.resource (.state .instances))
  if state.assembly.generation != state.generationBase + state.branch.programVersion then
    throw .malformed
  let some request := request? limits state action | throw .stale
  let (invocation, assembly) ← state.assembly.invokeWithin limits.executable request
    |>.mapError Error.executable
  match preflightBatch limits invocation.result with
  | .error error => throw error
  | .ok _ => pure ⟨⟩
  if invocation.rule != action.key || eventQuotes invocation.result.events != invocation.quotes then
    throw .malformed
  /- Structural events extend the exact post-callback assembly, preserving
  the cache returned by that same single invocation. -/
  let invoked := makeState assembly state.branch state.arena state.generationBase
    state.serial state.instances
  let cursor ← applyEvents limits invoked action invocation.result
  let next := makeState cursor.assembly cursor.branch (makeArena cursor.equalities)
    state.generationBase (state.serial + 1) cursor.instances
  let applied := makeApplied state.branch cursor.branch state.assembly.bindings
    cursor.assembly.bindings state.assembly.applications cursor.assembly.applications
    state.assembly.generation cursor.assembly.generation state.arena.items cursor.equalities
    action invocation.result.events invocation.quotes state.serial
  pure (applied, next)

private def commonMatcherEpoch? (applications : Array Executable.Application) : Option Nat := do
  let mut epoch : Option Nat := none
  for application in applications do
    match application.matcherEpoch, epoch with
    | none, _ => pure ()
    | some current, none => epoch := some current
    | some current, some expected => if current != expected then failure
  pure (epoch.getD 0)

private def offerRequest? (state : State Fact Cause) (id : ApplicationId) :
    Option (RuleRequest Fact) := do
  let application ← state.assembly.applications[id.index]?
  let registration ← state.assembly.registry.registrations[application.rule.index]?
  let seen ← application.watches.mapM fun node => do
    let version ← state.branch.versions[node.index]?
    pure { node, version }
  let inputs ← inputViews state.branch seen
  let action : Action :=
    { serial := state.serial
      programVersion := state.branch.programVersion
      application := id
      rule := application.rule
      key := registration.key
      node := application.node
      kind := application.kind
      effort := application.effort
      generation := application.generation
      inputs := inputs.map fun input => { node := input.node, version := input.version }
      writes := application.writes
      structuralInputs := application.structuralInputs
      matcherEpoch := application.matcherEpoch }
  pure
    { action
      program :=
        { programVersion := state.branch.programVersion
          operations := state.branch.program.operations
          nodes := state.branch.program.nodes
          generations := state.branch.generations
          depths := state.branch.depths }
      inputs
      writes := application.writes }

private def remaining (limit used : Nat) : Nat := limit - used

/-- Exact residual resources owned by this runtime representation. Matcher
visits, retained suggestions, and queue entries have no accumulating store in
this runtime layer, so their full configured capacities remain available. -/
private def budgetView (limits : Limits) (state : State Fact Cause) :
    Policy.EngineBudgetView :=
  let stateLimits := limits.executable.state
  { actions := remaining stateLimits.maxActions state.serial
    matcherVisits := stateLimits.maxMatcherVisits
    acceptedFacts := remaining stateLimits.maxAcceptedFacts state.branch.history.size
    nodes := remaining stateLimits.maxNodes state.branch.program.nodes.size
    applications := remaining stateLimits.maxApplications state.assembly.applications.size
    equalities := remaining stateLimits.maxEqualities state.arena.items.size
    retainedSuggestions := stateLimits.maxRetainedSuggestions
    instances := remaining stateLimits.maxInstances state.instances
    queueEntries := stateLimits.maxQueueEntries
    generation := remaining stateLimits.maxGeneration state.assembly.generation }

private def schedulerCompatible (action : Action) : Bool :=
  allDistinct action.writes && allDistinct action.structuralInputs

/-- Regenerate the complete deterministic executable offer snapshot from the
exact assembly, branch, equality arena, and callback serial owned by this
runtime state. Handler applicability sees one authenticated whole-state
context. Its Boolean is an intentional scheduling filter, not mutation
authorization: it can suppress an offer without making the snapshot
incomplete, while a separately supplied structurally current action is still
decided only by `stepWithin`. Repeated ordered reads can enter Search: every
occurrence retains its exact node/version and later request reconstruction
preserves the list. Runtime-valid applications with duplicate writes remain
omitted and set the sealed incomplete bit. The current sealed Executable
compiler produces no structural matcher rows; the same omission applies to a
future retained row with duplicate structural inputs.
No mutable branch or assembly replacement is accepted from the caller, and no
generated action bypasses the later exact `stepWithin` request reconstruction.
Snapshot generation does not consume or reject the runtime `maxActions`
budget; that budget is charged only when an action advances the state.

The reference implementation checks the retained branch/program once, then
scans the flat application table and its bounded ports once. Package
applicability and equality on caller facts remain non-preemptible. -/
opaque State.offerSnapshotWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (maxOffers : Nat) (state : State Fact Cause) :
    Except Error (OfferSnapshot Fact Cause) := do
  match state.assembly.preflightWithin limits.executable with
  | .error error => throw (.executable error)
  | .ok _ => pure ⟨⟩
  match preflightBranch limits.executable.state state.branch with
  | .error error => throw error
  | .ok _ => pure ⟨⟩
  if state.branch.program != state.assembly.program ||
      state.assembly.generation != state.generationBase + state.branch.programVersion ||
      limits.executable.state.maxEqualities < state.arena.items.size then
    throw .malformed
  let some snapshot := state.branch.checkedSnapshot? | throw .malformed
  let program : ProgramView :=
    { programVersion := state.branch.programVersion
      operations := state.branch.program.operations
      nodes := state.branch.program.nodes
      generations := state.branch.generations
      depths := state.branch.depths }
  let some context := state.assembly.offerContext? snapshot program | throw .malformed
  let some matcherEpoch := commonMatcherEpoch? state.assembly.applications | throw .malformed
  let mut actions := #[]
  let mut incomplete := false
  for index in [0:state.assembly.applications.size] do
    let id : ApplicationId := { index }
    let some request := offerRequest? state id | throw .malformed
    if context.offers request then
      if schedulerCompatible request.action then
        if maxOffers ≤ actions.size then throw (.resource .offers)
        actions := actions.push request.action
      else
        incomplete := true
  pure
    { branch := state.branch
      rules := state.assembly.registry.registrations
      bindings := state.assembly.bindings
      applicationGenerations := state.assembly.applications.map (fun application =>
        application.generation)
      equalityGenerations := state.arena.items.map (fun equality => equality.generation)
      matcherEpoch
      serial := state.serial
      remaining := budgetView limits state
      incomplete
      actions }

/-- Execute one exact structurally authenticated action once and regenerate
offers from the returned sticky-cache successor as a single sealed value. The
action need not have survived the package's scheduling-only `offers` filter;
`stepWithin` reconstructs its exact request and owns execution authority. If
successor offer generation fails, no replacement runtime state is returned. -/
opaque State.advanceWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (maxOffers : Nat) (state : State Fact Cause) (action : Action) :
    Except Error (Advanced Fact Cause) :=
  match state.stepWithin limits action with
  | .error error => .error error
  | .ok (transition, next) =>
      match next.offerSnapshotWithin limits maxOffers with
      | .error error => .error error
      | .ok offers => .ok { transition, state := next, offers }

end Hex.Interval.Runtime
