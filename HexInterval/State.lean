/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Trace

@[expose] public section

/-!
# Function-agnostic controller state

These contracts describe immutable branch facts, exact versioned updates,
dependency/queue alignment, and explicit controller limits. They deliberately
do not choose persistent storage, rollback, a priority policy, callbacks, or a
proof format. A value is plain decoded data until its `check` succeeds.

All builders are transactional: malformed, stale, or over-budget inputs return
an error and no replacement state. Runtime facts and provenance remain
untrusted data; only later theorem replay can establish their meaning.
-/

namespace Hex.Interval.State

/-- A single scheduler queue carries rule applications and equality
contractors without interpreting either. -/
inductive Work where
  | application (application : ApplicationId)
  | equality (equality : EqualityId)
  deriving DecidableEq, Repr

/-- Solver-owned resource whose checked limit was exhausted. -/
inductive Resource where
  | operations
  | nodes
  | rules
  | arity
  | scopes
  | applications
  | queueEntries
  | actions
  | matcherVisits
  | effort
  | registryEntries
  | replayFormats
  | acceptedFacts
  | retainedSuggestions
  | outcomeCandidates
  | outcomeSuggestions
  | instances
  | generation
  | nodeDepth
  | equalities
  deriving DecidableEq, Repr

/-- Independent structural and logical-work limits. Byte-bounded retained
diagnostics use `Hex.Interval.Trace.Limit`; arbitrary callback/Fact allocation is outside
this preemptible envelope. -/
structure Limits where
  maxOperations : Nat
  maxNodes : Nat
  maxRules : Nat
  maxRegistryEntries : Nat
  maxReplayFormats : Nat
  maxArity : Nat
  maxScopeNodes : Nat := 0
  maxApplications : Nat
  maxQueueEntries : Nat
  maxActions : Nat
  maxMatcherVisits : Nat := 0
  matcherBatchSize : Nat := 0
  maxAcceptedFacts : Nat
  maxRetainedSuggestions : Nat
  maxEffort : Nat
  maxObservationValue : Nat
  maxDiagnosticValue : Nat
  maxOutcomeCandidates : Nat
  maxOutcomeSuggestions : Nat
  maxProposalItems : Nat
  maxInstances : Nat
  maxGeneration : Nat
  maxNodeDepth : Nat
  maxEqualities : Nat
  splitEndpointLimit : EndpointLimit
  deriving DecidableEq, Repr

/-- Logical counters; these are telemetry and resource state, never proof
evidence. -/
structure Metrics where
  queueInsertions : Nat := 0
  suppressedInsertions : Nat := 0
  queuePops : Nat := 0
  requests : Nat := 0
  matcherVisits : Nat := 0
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
  droppedSuggestions : Nat := 0
  capacityDrops : Nat := 0
  depthDrops : Nat := 0
  generatedNodes : Nat := 0
  generatedScopes : Nat := 0
  generatedEqualities : Nat := 0
  equalityRuns : Nat := 0
  equalityImprovements : Nat := 0
  deriving DecidableEq, Repr

/-- One exact fact update with opaque caller-selected provenance. -/
structure Update (Fact Cause : Type) where
  programVersion : Nat
  node : NodeId
  previous : SeenVersion
  fact : Fact
  version : Nat
  cause : Cause

/-- Immutable fact state for one search branch. Base facts and appended-node
seeds are the authoritative version-zero facts; later current facts are
reconstructed from append-only history. Generation values are aligned bounded
metadata supplied by the controller, not independently authenticated theorem
provenance. -/
structure Branch (Fact Cause : Type) where
  programVersion : Nat
  baseProgram : Program
  initialFacts : Array Fact
  program : Program
  /-- Exact version-zero facts for the appended node suffix only. -/
  seeds : Array Fact
  versions : Array Nat
  generations : Array Nat
  depths : Array Nat
  history : Array (Update Fact Cause)
  contradictory : Bool

inductive BranchError where
  | invalidProgram
  | wrongFactCount
  | staleVersion (node : NodeId)
  | wrongProgramVersion
  | invalidGeneration
  | nonExtension
  | resource (resource : Resource)
  deriving DecidableEq, Repr

def programPrefix (before after : Program) : Bool := Id.run do
  if before.operations != after.operations || after.nodes.size < before.nodes.size then
    return false
  for index in [0:before.nodes.size] do
    if before.nodes[index]? != after.nodes[index]? then return false
  return true

namespace Branch

/-- Construct an exact version-zero branch. Structural caps are checked before
the depth, generation, and version arrays are allocated. -/
def startWithin (limits : Limits) (program : Program) (facts : Array Fact) :
    Except BranchError (Branch Fact Cause) := do
  if limits.maxOperations < program.operations.size then throw (.resource .operations)
  if limits.maxNodes < program.nodes.size then throw (.resource .nodes)
  if program.operations.any (fun operation => limits.maxArity < operation.inputs.length) ||
      program.nodes.any (fun node => limits.maxArity < node.args.length) then
    throw (.resource .arity)
  if facts.size != program.nodes.size then throw .wrongFactCount
  if !program.check then throw .invalidProgram
  let some depths := program.depths? | throw .invalidProgram
  if depths.any (fun depth => limits.maxNodeDepth < depth) then
    throw (.resource .nodeDepth)
  pure
    { programVersion := 0
      baseProgram := program
      initialFacts := facts
      program
      seeds := #[]
      versions := Array.replicate facts.size 0
      generations := Array.replicate facts.size 0
      depths
      history := #[]
      contradictory := false }

/-- Reconstruct current facts from the authoritative base/suffix seeds and
ordered update history. An out-of-range retained update is malformed. -/
def restoredFacts? (branch : Branch Fact Cause) : Option (Array Fact) := do
  if branch.initialFacts.size != branch.baseProgram.nodes.size ||
      branch.program.nodes.size < branch.baseProgram.nodes.size ||
      branch.seeds.size != branch.program.nodes.size - branch.baseProgram.nodes.size then
    none
  let mut facts := branch.initialFacts ++ branch.seeds
  for event in branch.history do
    if branch.program.nodes[event.node.index]?.isNone then none
    facts := facts.set! event.node.index event.fact
  pure facts

/-- Immutable callback-facing current fact snapshot. A malformed decoded
branch produces an empty fact array and consequently fails `Branch.check`. -/
def snapshot (branch : Branch Fact Cause) : Snapshot Fact :=
  { facts := branch.restoredFacts?.getD #[]
    versions := branch.versions
    contradictory := branch.contradictory }

/-- Resolve an exact retained version. Version zero comes from the immutable
seed array; later versions come only from append-only update history. -/
def factAt? (branch : Branch Fact Cause) (seen : SeenVersion) : Option Fact :=
  if seen.version == 0 then
    if seen.node.index < branch.initialFacts.size then
      branch.initialFacts[seen.node.index]?
    else
      branch.seeds[seen.node.index - branch.initialFacts.size]?
  else
    (branch.history.find? fun event =>
      event.node == seen.node && event.version == seen.version).map (·.fact)

/-- Reconstruct current node versions from exact predecessor links. -/
def restoredVersions? (branch : Branch Fact Cause) : Option (Array Nat) := do
  let mut versions := Array.replicate branch.program.nodes.size 0
  for event in branch.history do
    if branch.programVersion < event.programVersion || event.previous.node != event.node then
      none
    let current <- versions[event.node.index]?
    if event.previous.version != current || event.version != current + 1 then none
    versions := versions.set! event.node.index event.version
  pure versions

/-- Validate the generation facts that this generic state layer can establish:
base nodes are generation zero, and no appended node claims a generation after
the current append-only program version. Exact dependency-derived generation
is authenticated by the controller's instance transition, not by this table. -/
def generationsCheck (branch : Branch Fact Cause) : Bool := Id.run do
  if branch.generations.size != branch.program.nodes.size then return false
  for index in [0:branch.generations.size] do
    let some generation := branch.generations[index]? | return false
    if index < branch.baseProgram.nodes.size then
      if generation != 0 then return false
    else if branch.programVersion < generation then
      return false
  return true

/-- Validate all immutable array alignments, append-only program structure,
depths, and exact per-node update chronology. -/
def check (branch : Branch Fact Cause) : Bool :=
  let snapshot := branch.snapshot
  branch.baseProgram.check && branch.program.check &&
    programPrefix branch.baseProgram branch.program &&
    branch.initialFacts.size == branch.baseProgram.nodes.size &&
    branch.seeds.size == branch.program.nodes.size - branch.baseProgram.nodes.size &&
    snapshot.facts.size == branch.program.nodes.size &&
    snapshot.versions.size == branch.program.nodes.size &&
    branch.generationsCheck &&
    branch.program.depths? == some branch.depths &&
    branch.restoredVersions? == some branch.versions

/-- Install one already-computed update only when it names the exact live
predecessor and current program version. -/
def pushWithin (limits : Limits) (branch : Branch Fact Cause) (event : Update Fact Cause)
    (contradiction : Bool := false) : Except BranchError (Branch Fact Cause) := do
  if limits.maxAcceptedFacts <= branch.history.size then
    throw (.resource .acceptedFacts)
  if limits.maxOperations < branch.baseProgram.operations.size then
    throw (.resource .operations)
  if limits.maxNodes < branch.baseProgram.nodes.size then throw (.resource .nodes)
  if limits.maxOperations < branch.program.operations.size then
    throw (.resource .operations)
  if limits.maxNodes < branch.program.nodes.size then throw (.resource .nodes)
  if !branch.check then throw .invalidProgram
  if event.programVersion != branch.programVersion then throw .wrongProgramVersion
  let some current := branch.versions[event.node.index]? | throw (.staleVersion event.node)
  if event.previous.node != event.node || event.previous.version != current ||
      event.version != current + 1 then
    throw (.staleVersion event.node)
  pure
    { branch with
      versions := branch.versions.set! event.node.index event.version
      history := branch.history.push event
      contradictory := branch.contradictory || contradiction }

/-- Append one checked program suffix and its version-zero top facts. -/
def extendWithin (limits : Limits) (branch : Branch Fact Cause) (program : Program)
    (freshFacts : Array Fact) (generation : Nat) : Except BranchError (Branch Fact Cause) := do
  if limits.maxAcceptedFacts < branch.history.size then
    throw (.resource .acceptedFacts)
  if limits.maxOperations < program.operations.size then throw (.resource .operations)
  if limits.maxNodes < program.nodes.size then throw (.resource .nodes)
  if limits.maxOperations < branch.baseProgram.operations.size then
    throw (.resource .operations)
  if limits.maxNodes < branch.baseProgram.nodes.size then throw (.resource .nodes)
  if limits.maxOperations < branch.program.operations.size then
    throw (.resource .operations)
  if limits.maxNodes < branch.program.nodes.size then throw (.resource .nodes)
  if limits.maxGeneration < generation then throw (.resource .generation)
  if program.operations.any (fun operation => limits.maxArity < operation.inputs.length) ||
      program.nodes.any (fun node => limits.maxArity < node.args.length) then
    throw (.resource .arity)
  if !branch.check then throw .invalidProgram
  if !program.check || !programPrefix branch.program program then throw .nonExtension
  let added := program.nodes.size - branch.program.nodes.size
  if freshFacts.size != added then throw .wrongFactCount
  if 0 < added && (generation == 0 || branch.programVersion + 1 < generation) then
    throw .invalidGeneration
  let some depths := program.depths? | throw .invalidProgram
  if depths.any (fun depth => limits.maxNodeDepth < depth) then
    throw (.resource .nodeDepth)
  pure
    { branch with
      programVersion := branch.programVersion + 1
      program
      seeds := branch.seeds ++ freshFacts
      versions := branch.versions ++ Array.replicate added 0
      generations := branch.generations ++ Array.replicate added generation
      depths }

end Branch

/-- Dependency watchers and exact dirty bits. -/
structure Dependencies where
  watchers : Array (List Work)
  queued : Array Bool
  equalityQueued : Array Bool

namespace Dependencies

def workValid (applicationCount equalityCount : Nat) : Work -> Bool
  | .application application => application.index < applicationCount
  | .equality equality => equality.index < equalityCount

/-- Validate node alignment and every compact dependency reference. -/
def check (dependencies : Dependencies) (nodeCount applicationCount equalityCount : Nat) : Bool :=
  dependencies.watchers.size == nodeCount &&
    dependencies.queued.size == applicationCount &&
    dependencies.equalityQueued.size == equalityCount &&
    dependencies.watchers.all fun items =>
      items.all (workValid applicationCount equalityCount)

end Dependencies

/-- Append-only work log, per-occurrence liveness, and the first unconsumed
position. A cleared occurrence stays a tombstone even if the same work is
woken and appended again later. -/
structure Queue where
  queue : Array Work
  live : Array Bool
  queueHead : Nat

namespace Queue

inductive Error where
  | malformed
  | resource (resource : Resource)
  deriving DecidableEq, Repr

def containsAfter (queue : Queue) (work : Work) : Bool := Id.run do
  for index in [queue.queueHead:queue.queue.size] do
    if queue.live[index]? == some true && queue.queue[index]? == some work then return true
  return false

def dirty? (dependencies : Dependencies) : Work -> Option Bool
  | .application application => dependencies.queued[application.index]?
  | .equality equality => dependencies.equalityQueued[equality.index]?

/-- Validate the retained cap, cursor, compact references, and the bijection
between dirty bits and live retained suffix occurrences. Per-occurrence live
bits keep a policy-created tombstone dead after later re-enqueue. -/
def check (queue : Queue) (dependencies : Dependencies)
    (nodeCount applicationCount equalityCount maxEntries : Nat) : Bool := Id.run do
  if maxEntries < queue.queue.size || queue.queue.size < queue.queueHead ||
      queue.live.size != queue.queue.size ||
      !dependencies.check nodeCount applicationCount equalityCount then
    return false
  let mut seenApplications := Array.replicate applicationCount false
  let mut seenEqualities := Array.replicate equalityCount false
  for index in [0:queue.queue.size] do
    let some work := queue.queue[index]? | return false
    if !Dependencies.workValid applicationCount equalityCount work then return false
    let some live := queue.live[index]? | return false
    if index < queue.queueHead && live then return false
    if live then
      match work with
      | .application application =>
          if seenApplications[application.index]? != some false ||
              dependencies.queued[application.index]? != some true then
            return false
          seenApplications := seenApplications.set! application.index true
      | .equality equality =>
          if seenEqualities[equality.index]? != some false ||
              dependencies.equalityQueued[equality.index]? != some true then
            return false
          seenEqualities := seenEqualities.set! equality.index true
  return seenApplications == dependencies.queued &&
    seenEqualities == dependencies.equalityQueued

/-- Construct the initial application queue only after its retained-count
limit has admitted the entire allocation. -/
def initialWithin (maxEntries applicationCount : Nat) : Except Resource Queue := do
  if maxEntries < applicationCount then throw .queueEntries
  let mut queue := #[]
  for index in [0:applicationCount] do
    queue := queue.push (.application { index })
  pure { queue, live := Array.replicate applicationCount true, queueHead := 0 }

/-- Transactionally enqueue one valid work item, suppressing an already-live
item and setting exactly its aligned dirty bit. -/
def enqueueWithin (maxEntries nodeCount applicationCount equalityCount : Nat)
    (dependencies : Dependencies) (queue : Queue) (work : Work) :
    Except Error (Dependencies × Queue) := do
  if !queue.check dependencies nodeCount applicationCount equalityCount maxEntries ||
      !Dependencies.workValid applicationCount equalityCount work then
    throw Error.malformed
  let some dirty := dirty? dependencies work | throw Error.malformed
  if dirty then return (dependencies, queue)
  if maxEntries <= queue.queue.size then throw (Error.resource .queueEntries)
  let dependencies := match work with
    | .application application =>
        { dependencies with queued := dependencies.queued.set! application.index true }
    | .equality equality =>
        { dependencies with
          equalityQueued := dependencies.equalityQueued.set! equality.index true }
  pure (dependencies,
    { queue with queue := queue.queue.push work, live := queue.live.push true })

/-- Transactionally clear one selected work item. Its retained queue-log entry
may become a tombstone; a later enqueue appends a fresh occurrence. -/
def deactivate (maxEntries nodeCount applicationCount equalityCount : Nat)
    (dependencies : Dependencies) (queue : Queue) (work : Work) :
    Except Error (Dependencies × Queue) := do
  if !queue.check dependencies nodeCount applicationCount equalityCount maxEntries ||
      !Dependencies.workValid applicationCount equalityCount work then
    throw Error.malformed
  let some dirty := dirty? dependencies work | throw Error.malformed
  if !dirty then throw Error.malformed
  let mut liveIndex? := none
  for index in [queue.queueHead:queue.queue.size] do
    if queue.live[index]? == some true && queue.queue[index]? == some work then
      liveIndex? := some index
      break
  let some liveIndex := liveIndex? | throw Error.malformed
  let dependencies := match work with
    | .application application =>
        { dependencies with queued := dependencies.queued.set! application.index false }
    | .equality equality =>
        { dependencies with
          equalityQueued := dependencies.equalityQueued.set! equality.index false }
  pure (dependencies, { queue with live := queue.live.set! liveIndex false })

/-- Transactionally pop the next still-dirty work item, skipping retained
tombstones created by policy selection. `none` denotes a checked empty suffix;
the returned queue still commits the cursor advance across those tombstones. -/
def pop (maxEntries nodeCount applicationCount equalityCount : Nat)
    (dependencies : Dependencies) (queue : Queue) :
    Except Error (Option Work × Dependencies × Queue) := do
  if !queue.check dependencies nodeCount applicationCount equalityCount maxEntries then
    throw Error.malformed
  let mut queue := queue
  while queue.queueHead < queue.queue.size do
    let some work := queue.queue[queue.queueHead]? | throw Error.malformed
    let some live := queue.live[queue.queueHead]? | throw Error.malformed
    if live then
      let (dependencies, deactivated) <-
        queue.deactivate maxEntries nodeCount applicationCount equalityCount dependencies work
      queue := { deactivated with queueHead := deactivated.queueHead + 1 }
      if !queue.check dependencies nodeCount applicationCount equalityCount maxEntries then
        throw Error.malformed
      return (some work, dependencies, queue)
    queue := { queue with queueHead := queue.queueHead + 1 }
  pure (none, dependencies, queue)

end Queue
end Hex.Interval.State
