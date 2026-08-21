/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.BranchProof
import HexInterval.Experiment.ExpSign
import Lean.Elab.Tactic.Basic

/-!
# Nested branch scheduling conformance

This Mathlib-free canary builds a live two-level split tree.  The left child
splits a second source while the right child closes immediately, so the child
policy fork is genuinely side-sensitive and depth-first and breadth-first
frontiers differ on live pending work.
-/

namespace Hex.Interval.NestedBranchConformance

local notation "OfferView" =>
  Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey
local notation "Selection" =>
  Hex.Interval.Policy.Decision _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey
local notation "ScopeId" => Hex.Interval.Policy.ScopeId
local notation "OfferClass" => Hex.Interval.Policy.OfferClass

open Lean Elab Tactic Meta
open Hex.Interval
open Experiment
open Propagator PolicySession SemanticReplay TargetRun BranchStart BranchTree
open BranchProof ExpSign

private def program : Program :=
  { operations
    nodes := #[sourceInstruction, sourceInstruction, expInstruction] }

private def target : NodeFact Bound :=
  { node := node 2, fact := .nonnegative }

private def input : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.all, .all, .all]
    target }

private inductive Route where
  | root
  | splitLeft
  | close
  deriving DecidableEq, Repr

private def splitAt (wanted : NodeId) (view : (Hex.Interval.Policy.View Bound _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey)) :
    Option OfferView :=
  view.offers.toList.find? fun offer =>
    match offer.key with
    | .invoke invocation =>
        invocation.rule == splitRuleKey && invocation.anchor == wanted
    | .split _ seen _ _ => seen.node == wanted
    | _ => false

private def expAt (wanted : NodeId) (view : (Hex.Interval.Policy.View Bound _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey)) :
    Option OfferView :=
  view.offers.toList.find? fun offer =>
    match offer.key with
    | .invoke invocation =>
        invocation.rule == expRuleKey && invocation.anchor == wanted
    | _ => false

private def controller : Controller Bound Route :=
  { update := fun state _ => state
    choose := fun state view =>
      let selected :=
        match state with
        | .root => splitAt (node 0) view
        | .splitLeft => splitAt (node 1) view
        | .close => expAt (node 2) view
      match selected with
      | some offer => .select offer state
      | none => .stop state }

private def fork : Route -> Side -> Route
  | .root, .left => .splitLeft
  | .root, .right => .close
  | .splitLeft, _ => .close
  | .close, _ => .close

private def splitter : Splitter Bound :=
  { split := fun graph splitNode instruction parent point =>
      if graph.node? splitNode == some instruction &&
          instruction.domain == real && parent == .all && point == 0 then
        some (.nonnegative, .negative)
      else
        none }

private def resources : Search.Limits :=
  { maxSteps := 5
    maxSplits := 2
    maxLeaves := 3
    maxFrontier := 3
    maxDepth := 3
    maxScopes := 5
    leafFuel := limits.policy.maxDecisions }

private def config (order : Search.Order) : Config Bound Route :=
  { factDomain
    packages := splitPackages
    sessionLimits := limits
    controller
    splitter
    forkPolicy := fork
    order
    limits := resources }

private def run? (order : Search.Order) (fuel : Nat) : Option (State Bound Route) := do
  let .ok state := BranchTree.start (config order) { index := 0 } input .root
    | none
  let .ok state := BranchTree.runFrom (config order) fuel state | none
  some state

private def leafReached? (entry : BranchTree.Node Bound Route) : Bool :=
  match entry with
  | .leaf source (.result result) =>
      source.input.target == target &&
        match result.stop with
        | .target reached => reached.seen.node == target.node &&
            reached.fact == .nonnegative
        | _ => false
  | _ => false

#guard fork .root .left == .splitLeft
#guard fork .root .right == .close

#guard
  (run? .depthFirst 2).any fun state =>
    state.accounting.steps == 2 && state.accounting.splits == 2 && state.accounting.leaves == 3 &&
      state.frontier.pending == [{ index := 3 }, { index := 4 }, { index := 2 }]

#guard
  (run? .breadthFirst 2).any fun state =>
    state.accounting.steps == 2 && state.accounting.splits == 2 && state.accounting.leaves == 3 &&
      state.frontier.pending == [{ index := 2 }, { index := 3 }, { index := 4 }]

#guard
  (run? .depthFirst 5).any fun state =>
    state.settled && state.accounting.steps == 5 && state.accounting.splits == 2 &&
      state.accounting.leaves == 3 && state.nodes.size == 5 &&
      match state.nodes[0]?, state.nodes[1]?, state.nodes[2]?,
          state.nodes[3]?, state.nodes[4]? with
      | some (BranchTree.Node.split root _ rootChildren left right),
          some (BranchTree.Node.split nested _ nestedChildren nestedLeft nestedRight),
          some rightLeaf, some nestedLeftLeaf, some nestedRightLeaf =>
          root.policyState == .root && left.index == 1 && right.index == 2 &&
            rootChildren.leftScope.index == 1 &&
            rootChildren.rightScope.index == 2 &&
            rootChildren.left.initialFacts == #[.nonnegative, .all, .all] &&
            rootChildren.right.initialFacts == #[.negative, .all, .all] &&
            nested.policyState == .splitLeft &&
            nestedLeft.index == 3 && nestedRight.index == 4 &&
            nestedChildren.leftScope.index == 3 &&
            nestedChildren.rightScope.index == 4 &&
            nestedChildren.left.initialFacts ==
              #[.nonnegative, .nonnegative, .all] &&
            nestedChildren.right.initialFacts ==
              #[.nonnegative, .negative, .all] &&
            leafReached? rightLeaf && leafReached? nestedLeftLeaf &&
            leafReached? nestedRightLeaf
      | _, _, _, _, _ => false

#guard
  (run? .breadthFirst 5).any fun state =>
    state.settled && state.accounting.steps == 5 && state.accounting.splits == 2 &&
      state.accounting.leaves == 3 && state.nodes.size == 5 &&
      state.nodes.toList.countP leafReached? == 3

/-! ## Propagate before splitting -/

private def postProgram : Program :=
  { operations
    nodes := #[sourceInstruction, expInstruction, expInstruction] }

private def postTarget : NodeFact Bound :=
  { node := node 2, fact := .nonnegative }

private def postInput : CheckerInput Bound :=
  { baseProgram := postProgram
    initialFacts := #[.all, .all, .all]
    target := postTarget }

private inductive PostRoute where
  | improve
  | split
  | close
  deriving DecidableEq, Repr

private def postController : Controller Bound PostRoute :=
  { update := fun state event =>
      match state, event with
      | .improve, .rule _ => .split
      | state, _ => state
    choose := fun state view =>
      let selected :=
        match state with
        | .improve => expAt (node 1) view
        | .split => splitAt (node 0) view
        | .close => expAt (node 2) view
      match selected with
      | some offer => .select offer state
      | none => .stop state }

private def postFork (_ : PostRoute) (_ : Side) : PostRoute := .close

private def postResources : Search.Limits :=
  { maxSteps := 3
    maxSplits := 1
    maxLeaves := 2
    maxFrontier := 2
    maxDepth := 1
    maxScopes := 3
    leafFuel := limits.policy.maxDecisions }

private def postConfig : Config Bound PostRoute :=
  { factDomain
    packages := splitPackages
    sessionLimits := limits
    controller := postController
    splitter
    forkPolicy := postFork
    order := .depthFirst
    limits := postResources }

private def postTree? : Option (State Bound PostRoute) := do
  let .ok state := BranchTree.start postConfig { index := 0 } postInput .improve
    | none
  let .ok state := BranchTree.run postConfig state | none
  some state

/- The split parent is the exact post-propagation snapshot. It intentionally
differs from the run's starting input at the unrelated exponential node. -/
#guard
  postTree?.any fun tree =>
    tree.settled && tree.nodes.size == 3 &&
      match tree.nodes[0]? with
      | some (BranchTree.Node.split source result children _ _) =>
          !BranchProof.sameInput source.input children.parent &&
            BranchProof.sameParent source result children.parent &&
            children.parent.initialFacts == #[.all, .nonnegative, .all] &&
            match result.stop with
            | .split plan => BranchProof.samePlan plan children.plan
            | _ => false
      | _ => false

private def trueEmitter : BranchProof.Emitter Bound PostRoute :=
  { leaf := fun _ _ => pure (mkConst ``True.intro)
    split := fun _ _ _ _ _ => pure (mkConst ``True.intro) }

private def postProofLimits : BranchProof.Limits :=
  { maxNodes := 3, maxDepth := 1 }

/-- The generic fold accepts a live tree whose parent performed a fact
improvement before subdividing. -/
example : True := by
  run_tac
    let some tree := postTree?
      | throwError "interval post-run split: runtime tree failed"
    let goal ← getMainGoal
    goal.assign (← BranchProof.emit postProofLimits trueEmitter tree
      (← goal.getType))

example : True := by
  run_tac
    let some tree := postTree?
      | throwError "interval post-run split mutation: runtime tree failed"
    let snapshot := tree.snapshot
    let some root := snapshot.nodes[0]?
      | throwError "interval post-run split mutation: root missing"
    let BranchTree.Node.split source result children left right := root
      | throwError "interval post-run split mutation: root is not split"
    let staleChildren := { children with parent := source.input }
    let stale :=
      { snapshot with
        nodes := snapshot.nodes.set! 0 (.split source result staleChildren left right) }
    if (← observing? <| BranchProof.emitSnapshot postProofLimits trueEmitter stale
        (mkConst ``True)).isSome then
      throwError "interval post-run split mutation: stale parent was accepted"
    let wrongPlan := { children.plan with point := 1 }
    let changedChildren := { children with plan := wrongPlan }
    let changed :=
      { snapshot with
        nodes := snapshot.nodes.set! 0 (.split source result changedChildren left right) }
    if (← observing? <| BranchProof.emitSnapshot postProofLimits trueEmitter changed
        (mkConst ``True)).isSome then
      throwError "interval post-run split mutation: changed plan was accepted"
    let wrongVersion := { children.plan with version := children.plan.version + 1 }
    let changedVersionChildren := { children with plan := wrongVersion }
    let changedVersion :=
      { snapshot with
        nodes := snapshot.nodes.set! 0
          (.split source result changedVersionChildren left right) }
    if (← observing? <| BranchProof.emitSnapshot postProofLimits trueEmitter changedVersion
        (mkConst ``True)).isSome then
      throwError "interval post-run split mutation: changed plan version was accepted"
  trivial

end Hex.Interval.NestedBranchConformance
