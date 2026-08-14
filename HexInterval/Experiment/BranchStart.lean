/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.TargetRun
public import HexInterval.Experiment.SemanticReplay

@[expose] public section

/-!
# Checked branch starts

This experiment turns one policy-owned split plan into two exact child
`CheckerInput`s.  It is representation- and function-independent: the fact
domain checks strict narrowing, while a registered splitter interprets the
domain-specific cut.

The transition is search infrastructure, not proof evidence.  The proof
frontend must still seed inherited parent evidence, add exactly one child
assumption, and replay a package-owned coverage theorem before joining the
children.
-/

namespace Hex.Interval.Experiment.BranchStart

open Propagator PolicySession SemanticReplay TargetRun

/-- Tree-wide branch resources, separate from each child session's own limits. -/
structure Limits where
  maxDepth : Nat
  maxScopes : Nat
  deriving DecidableEq, Repr

/-- Monotone identities, active-scope depths, and resource use owned by one
branch tree.  The private constructor prevents callers from choosing counters
or registering a scope at an invented depth. -/
structure State where
  private mk ::
  createdScopes : Nat
  nextScope : Nat
  private scopeDepths : List (Propagator.Policy.ScopeId × Nat)

private def makeState (createdScopes nextScope : Nat)
    (scopeDepths : List (Propagator.Policy.ScopeId × Nat)) : State :=
  { createdScopes, nextScope, scopeDepths }

namespace State

/-- Account for the already-existing root scope of this exact engine-owned
session.  The sealed result can advance only through `prepare`. -/
opaque start (session : Session Fact) : State :=
  makeState 1 (session.state.scope.index + 1) [(session.state.scope, 0)]

end State

/-- A domain package translates the executable cut into two proposed child
facts.  The generic manager independently checks that each proposal is the
exact result of a strict narrowing step. -/
structure Splitter (Fact : Type) where
  split : Program -> NodeId -> Node -> Fact -> Dyadic -> Option (Fact × Fact)

/-- Exact parent and child snapshots prepared by one accepted split. -/
structure Children (Fact : Type) where
  plan : Propagator.Policy.SplitPlan Fact
  depth : Nat
  parent : CheckerInput Fact
  leftScope : Propagator.Policy.ScopeId
  left : CheckerInput Fact
  rightScope : Propagator.Policy.ScopeId
  right : CheckerInput Fact

/-- Fail-closed reasons for refusing to create child sessions. -/
inductive Error where
  | inactive
  | incomplete
  | contradictory
  | wrongScope
  | wrongState
  | endpointLimit
  | unknownSuggestion
  | wrongSuggestion
  | wrongSuggestionVersion
  | wrongOrigin
  | staleProgram
  | staleOrigin
  | unknownNode
  | staleFact
  | staleVersion
  | unknownTarget
  | unsupportedCut
  | duplicateChild
  | leftNotStrict
  | rightNotStrict
  | depthLimit
  | scopeLimit
  deriving DecidableEq, Repr

def strictChild [DecidableEq Fact] (domain : FactDomain Fact) (instruction : Node)
    (parent child : Fact) : Bool :=
  match domain.narrow instruction.domain parent child with
  | .improved installed => installed == child
  | .noChange | .contradiction _ | .malformed _ | .resourceLimit _ => false

/-- Validate one retained split plan and allocate two fresh child scopes.

The child snapshots start from the parent's current program and complete fact
array, replacing only the split node.  Proof production must authenticate all
unchanged entries as inherited parent facts; this function never promotes
them to caller assumptions.  The state supplies the parent depth; a caller
cannot reset that depth independently of its registered scope. -/
opaque prepare [DecidableEq Fact] (limits : Limits) (state : State)
    (session : Session Fact) (plan : Propagator.Policy.SplitPlan Fact)
    (target : NodeFact Fact) (splitter : Splitter Fact) :
    Except Error (State × Children Fact) := do
  if !session.live then throw .inactive
  if session.droppedWork || session.state.incomplete then throw .incomplete
  if session.state.engine.contradictory then throw .contradictory
  if plan.scope != session.state.scope then throw .wrongScope
  let depth <-
    match state.scopeDepths.find? (fun entry => entry.1 == session.state.scope) with
    | some entry => pure entry.2
    | none => throw .wrongState
  let engine := session.state.engine
  if !(EndpointCost.ofDyadic plan.point).allowed engine.limits.splitEndpointLimit then
    throw .endpointLimit
  if plan.source != Propagator.Policy.invocationOfAction plan.scope plan.origin then
    throw .wrongOrigin
  let retained <-
    match engine.suggestions[plan.suggestion.index]? with
    | some retained => pure retained
    | none => throw .unknownSuggestion
  if retained.action != plan.origin then throw .wrongOrigin
  match retained.suggestion with
  | .split request =>
      if request.node != plan.node || request.point != plan.point ||
          request.reason != plan.reason then
        throw .wrongSuggestion
  | .retry _ | .instantiate _ => throw .wrongSuggestion
  if retained.splitVersion != some plan.version then throw .wrongSuggestionVersion
  if plan.origin.programVersion != engine.programVersion then throw .staleProgram
  if !engine.actionFresh plan.origin then throw .staleOrigin
  let instruction <-
    match engine.program.node? plan.node with
    | some instruction => pure instruction
    | none => throw .unknownNode
  let current <-
    match engine.facts[plan.node.index]? with
    | some fact => pure fact
    | none => throw .unknownNode
  if current != plan.fact then throw .staleFact
  let version <-
    match engine.versions[plan.node.index]? with
    | some version => pure version
    | none => throw .unknownNode
  if version != plan.version then throw .staleVersion
  if (engine.program.node? target.node).isNone then throw .unknownTarget
  let (leftFact, rightFact) <-
    match splitter.split engine.program plan.node instruction plan.fact plan.point with
    | some children => pure children
    | none => throw .unsupportedCut
  if leftFact == rightFact then throw .duplicateChild
  if !strictChild engine.factDomain instruction plan.fact leftFact then
    throw .leftNotStrict
  if !strictChild engine.factDomain instruction plan.fact rightFact then
    throw .rightNotStrict
  let childDepth := depth + 1
  if childDepth > limits.maxDepth then throw .depthLimit
  if state.createdScopes + 2 > limits.maxScopes then throw .scopeLimit
  let leftScope : Propagator.Policy.ScopeId := { index := state.nextScope }
  let rightScope : Propagator.Policy.ScopeId := { index := state.nextScope + 1 }
  let parent : CheckerInput Fact :=
    { baseProgram := engine.program, initialFacts := engine.facts, target }
  let left : CheckerInput Fact :=
    { parent with initialFacts := engine.facts.set! plan.node.index leftFact }
  let right : CheckerInput Fact :=
    { parent with initialFacts := engine.facts.set! plan.node.index rightFact }
  let remaining := state.scopeDepths.filter (fun entry => entry.1 != session.state.scope)
  let next := makeState (state.createdScopes + 2) (state.nextScope + 2)
    ((leftScope, childDepth) :: (rightScope, childDepth) :: remaining)
  pure (next,
    { plan, depth := childDepth, parent, leftScope, left, rightScope, right })

/-- Runtime classification of one child result.  `contradiction` is a search
status only; a proof-producing join still needs a checked refutation schema. -/
inductive LeafStatus (Fact : Type)
  | target (reached : TargetRun.Reached Fact)
  | contradiction
  | unfinished
  | wrongInput

def sameInput [DecidableEq Fact] (scope : Propagator.Policy.ScopeId)
    (input : CheckerInput Fact)
    (result : TargetRun.Result Fact PolicyState) : Bool :=
  result.session.state.scope == scope &&
    result.session.state.engine.baseProgram == input.baseProgram &&
    result.session.state.engine.initialFacts == input.initialFacts

/-- Classify a child only after binding its run back to the exact prepared
input.  Target closure is rechecked against the retained current fact and
version. -/
def status [DecidableEq Fact] (domain : FactDomain Fact)
    (scope : Propagator.Policy.ScopeId) (input : CheckerInput Fact)
    (result : TargetRun.Result Fact PolicyState) :
    LeafStatus Fact :=
  if !sameInput scope input result then .wrongInput
  else
    let engine := result.session.state.engine
    match result.stop with
    | .target reached =>
        if reached.seen.node != input.target.node then .unfinished
        else
          match engine.program.node? reached.seen.node,
              engine.facts[reached.seen.node.index]?,
              engine.versions[reached.seen.node.index]? with
          | some instruction, some fact, some version =>
              if fact != reached.fact || version != reached.seen.version then .unfinished
              else
                match domain.narrow instruction.domain fact input.target.fact with
                | .noChange => .target reached
                | .improved _ | .contradiction _ | .malformed _ | .resourceLimit _ =>
                    .unfinished
          | _, _, _ => .unfinished
    | .contradiction =>
        if engine.contradictory then .contradiction else .unfinished
    | _ => .unfinished

/-- Refuse the ordinary two-proof join unless both exact child runs reached
their requested targets.  Contradictory children deliberately do not pass:
they need proof-producing refutation before generic elimination is sound. -/
def closedTargets? [DecidableEq Fact] (domain : FactDomain Fact)
    (children : Children Fact)
    (left : TargetRun.Result Fact LeftState)
    (right : TargetRun.Result Fact RightState) :
    Option (TargetRun.Reached Fact × TargetRun.Reached Fact) :=
  match status domain children.leftScope children.left left,
      status domain children.rightScope children.right right with
  | .target left, .target right => some (left, right)
  | _, _ => none

end Hex.Interval.Experiment.BranchStart
