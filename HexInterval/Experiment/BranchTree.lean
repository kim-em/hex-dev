/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.BranchStart
public import HexInterval.Search

@[expose] public section

/-!
# Resource-bounded branch trees

This experiment retains a complete runtime tree while repeatedly running
ordinary target-directed sessions and expanding accepted split plans.  It is
generic in the fact domain, executable packages, and external policy state.

The tree is search data, not proof evidence.  In particular, a runtime
contradiction leaf is not a proof of `False`, and a pair of target leaves is
not a proof of their parent target.  The proof frontend must separately replay
each retained leaf and join checked child evidence through a split schema.
-/

namespace Hex.Interval.Experiment.BranchTree

open Propagator PolicySession SemanticReplay TargetRun BranchStart

/-- Which child is being initialized.  Policies may use this to fork private
state differently on the two sides. -/
inductive Side where
  | left
  | right
  deriving DecidableEq, Repr

/-- Everything needed to run and split one pending leaf. -/
structure Config (Fact PolicyState : Type) : Type 1 where
  factDomain : FactDomain Fact
  packages : Array (Package Fact)
  sessionLimits : PolicySession.Limits
  controller : TargetRun.Controller Fact PolicyState
  splitter : BranchStart.Splitter Fact
  forkPolicy : PolicyState -> Side -> PolicyState
  order : Hex.Interval.Search.Order
  limits : Hex.Interval.Search.Limits

/-- Stable index into the append-only node array. -/
structure TreeId where
  index : Nat
  deriving DecidableEq, Repr

/-- Exact input, scope, depth, and private policy state of one leaf. -/
structure Leaf (Fact PolicyState : Type) where
  scope : Hex.Interval.Policy.ScopeId
  depth : Nat
  input : CheckerInput Fact
  policyState : PolicyState

/-- A leaf whose policy session can still be run. -/
structure Job (Fact PolicyState : Type) : Type 1 where
  scope : Hex.Interval.Policy.ScopeId
  depth : Nat
  input : CheckerInput Fact
  policyState : PolicyState
  session : PolicySession.Session Fact

/-- Why a split result was retained as a blocked leaf. -/
inductive Blocked where
  | splitRejected (error : BranchStart.Error)
  | splitLimit
  | leafLimit
  | frontierLimit
  deriving DecidableEq, Repr

/-- Terminal runtime data for a leaf.  None of these constructors is proof
evidence. -/
inductive LeafEnd (Fact PolicyState : Type) : Type 1
  | result (run : TargetRun.Result Fact PolicyState)
  | blocked (run : TargetRun.Result Fact PolicyState) (reason : Blocked)
  | startError (error : PolicySession.StartError)

/-- One retained runtime-tree node.  A split node stores the exact validated
child snapshots and both child identities, even if a child session failed to
start. -/
inductive Node (Fact PolicyState : Type) : Type 1
  | pending (job : Job Fact PolicyState)
  | leaf (source : Leaf Fact PolicyState) (ending : LeafEnd Fact PolicyState)
  | split (source : Leaf Fact PolicyState)
      (run : TargetRun.Result Fact PolicyState)
      (children : BranchStart.Children Fact) (left right : TreeId)

/-- Monotone retained state for one tree.  `leaves` counts current leaves, so
an accepted binary split increases it by exactly one. -/
structure State (Fact PolicyState : Type) : Type 1 where
  private mk ::
  nodes : Array (Node Fact PolicyState)
  search : Hex.Interval.Search.FrontierState TreeId
  branch : BranchStart.State

def State.frontier (state : State Fact PolicyState) :
    Hex.Interval.Search.Frontier TreeId :=
  state.search.frontier

def State.accounting (state : State Fact PolicyState) :
    Hex.Interval.Search.Accounting :=
  state.search.accounting

/-- Read-only retained tree data supplied to the proof fold. This snapshot is
untrusted proof input: callers may edit it, and `BranchProof` must reject every
malformed coverage relation. It carries no live search accounting authority. -/
structure Snapshot (Fact PolicyState : Type) : Type 1 where
  nodes : Array (Node Fact PolicyState)
  frontier : Hex.Interval.Search.Frontier TreeId

def State.snapshot (state : State Fact PolicyState) : Snapshot Fact PolicyState :=
  { nodes := state.nodes, frontier := state.frontier }

/-- Failure before a coherent root tree exists. -/
inductive StartError where
  | leafLimit
  | frontierLimit
  | scopeLimit
  | unknownTarget
  | session (error : PolicySession.StartError)
  | accounting (error : Hex.Interval.Search.Error)
  deriving DecidableEq, Repr

/-- An append-only tree should only schedule valid pending nodes. -/
inductive Error where
  | missingNode (id : TreeId)
  | settledNode (id : TreeId)
  | malformedAccounting
  | wrongScope
  deriving DecidableEq, Repr

def sourceOf (job : Job Fact PolicyState) : Leaf Fact PolicyState :=
  { scope := job.scope
    depth := job.depth
    input := job.input
    policyState := job.policyState }

namespace State

/-- A tree is settled exactly when it has no runnable leaf.  It may still
contain blocked, unfinished, or failed leaves. -/
def settled (state : State Fact PolicyState) : Bool :=
  state.frontier.isEmpty

/-- The global processing budget may leave a nonempty frontier. -/
def stepLimited (limits : Hex.Interval.Search.Limits)
    (state : State Fact PolicyState) : Bool :=
  state.accounting.steps >= limits.maxSteps && !state.frontier.isEmpty

/-- Build a coherent root session from the exact caller input. -/
opaque start (config : Config Fact PolicyState) (scope : Hex.Interval.Policy.ScopeId)
    (input : CheckerInput Fact) (policyState : PolicyState) :
    Except StartError (State Fact PolicyState) := do
  if config.limits.maxLeaves = 0 then throw .leafLimit
  if config.limits.maxFrontier = 0 then throw .frontierLimit
  if config.limits.maxScopes = 0 then throw .scopeLimit
  if (input.baseProgram.node? input.target.node).isNone then
    throw StartError.unknownTarget
  let session <-
    match PolicySession.Session.start config.factDomain input.baseProgram
        config.packages input.initialFacts config.sessionLimits scope with
    | .ok session => pure session
    | .error error => throw (.session error)
  let root : Job Fact PolicyState :=
    { scope, depth := 0, input, policyState, session }
  match Hex.Interval.Search.FrontierState.startWithin config.limits scope ({ index := 0 } : TreeId) with
  | .error error => throw (.accounting error)
  | .ok search =>
      pure { nodes := #[.pending root], search, branch := BranchStart.State.start session }

def childNode (config : Config Fact PolicyState) (side : Side)
    (scope : Hex.Interval.Policy.ScopeId) (depth : Nat) (input : CheckerInput Fact)
    (policyState : PolicyState) : Node Fact PolicyState × Bool :=
  let childState := config.forkPolicy policyState side
  let source : Leaf Fact PolicyState := { scope, depth, input, policyState := childState }
  match PolicySession.Session.start config.factDomain input.baseProgram
      config.packages input.initialFacts config.sessionLimits scope with
  | .ok session =>
      (.pending
        { scope := source.scope
          depth := source.depth
          input := source.input
          policyState := source.policyState
          session }, true)
  | .error error => (.leaf source (.startError error), false)

private def retainLeaf (limits : Hex.Interval.Search.Limits)
    (state : State Fact PolicyState) (id : TreeId)
    (source : Leaf Fact PolicyState) (ending : LeafEnd Fact PolicyState) :
    Except Error (State Fact PolicyState) := do
  match state.search.settleHeadWithin limits with
  | .error _ => throw .malformedAccounting
  | .ok (settled, search) =>
      if settled != id then throw .malformedAccounting
      pure
        { nodes := state.nodes.set! id.index (.leaf source ending)
          search := search
          branch := state.branch }

/-- Process one pending leaf.  Split rejection and tree-resource exhaustion
are terminal leaf data; only a malformed internal frontier returns `Error`. -/
opaque step [DecidableEq Fact] (config : Config Fact PolicyState)
    (state : State Fact PolicyState) : Except Error (State Fact PolicyState) := do
  if !state.accounting.check config.limits state.frontier.pending.length then
    throw .malformedAccounting
  if state.accounting.steps >= config.limits.maxSteps then return state
  let some id := state.search.head? | return state
  let some node := state.nodes[id.index]? | throw (.missingNode id)
  let .pending job := node | throw (.settledNode id)
  let source := sourceOf job
  let run := TargetRun.drive config.factDomain job.input.target.node
    job.input.target.fact config.controller config.limits.leafFuel
    job.session job.policyState
  let .split plan := run.stop |
    return ← retainLeaf config.limits state id source (.result run)
  if state.accounting.splits >= config.limits.maxSplits then
    return ← retainLeaf config.limits state id source (.blocked run .splitLimit)
  if state.accounting.leaves + 1 > config.limits.maxLeaves then
    return ← retainLeaf config.limits state id source (.blocked run .leafLimit)
  if state.search.pending.length + 1 > config.limits.maxFrontier then
    return ← retainLeaf config.limits state id source (.blocked run .frontierLimit)
  let branchLimits : BranchStart.Limits :=
    { maxDepth := config.limits.maxDepth, maxScopes := config.limits.maxScopes }
  match BranchStart.prepare branchLimits state.branch run.session plan
      job.input.target config.splitter with
  | .error error =>
      retainLeaf config.limits state id source (.blocked run (.splitRejected error))
  | .ok (branch, children) =>
      if children.leftScope.index != state.accounting.nextScope ||
          children.rightScope.index != state.accounting.nextScope + 1 then
        throw .wrongScope
      let leftId : TreeId := { index := state.nodes.size }
      let rightId : TreeId := { index := state.nodes.size + 1 }
      let (leftNode, leftPending) := childNode config .left children.leftScope
        children.depth children.left run.policyState
      let (rightNode, rightPending) := childNode config .right children.rightScope
        children.depth children.right run.policyState
      let fresh :=
        (if leftPending then [leftId] else []) ++
          (if rightPending then [rightId] else [])
      match state.search.splitHeadWithin config.limits config.order fresh with
      | .error _ => throw .malformedAccounting
      | .ok (splitId, search) =>
          if splitId != id then throw .malformedAccounting
          pure
            { nodes := (state.nodes.set! id.index
                  (.split source run children leftId rightId)).push leftNode |>.push rightNode
              search
              branch }

/-- Run for at most the caller fuel and never beyond the retained global step
budget.  A nonempty frontier in the result is an honest partial tree. -/
def runFrom [DecidableEq Fact] (config : Config Fact PolicyState) :
    Nat -> State Fact PolicyState -> Except Error (State Fact PolicyState)
  | 0, state => pure state
  | fuel + 1, state =>
      if state.settled || state.accounting.steps >= config.limits.maxSteps then pure state
      else do
        let state ← step config state
        runFrom config fuel state

termination_by fuel _ => fuel

/-- Consume the configured global processing budget. -/
def run [DecidableEq Fact] (config : Config Fact PolicyState)
    (state : State Fact PolicyState) : Except Error (State Fact PolicyState) :=
  runFrom config config.limits.maxSteps state

end State

def start := @State.start

def step := @State.step

def run := @State.run

def runFrom := @State.runFrom

end Hex.Interval.Experiment.BranchTree
