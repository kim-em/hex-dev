/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.BranchTree
import HexInterval.Experiment.ExpSign

/-!
# Nested branch scheduling conformance

This Mathlib-free canary builds a live two-level split tree.  The left child
splits a second source while the right child closes immediately, so the child
policy fork is genuinely side-sensitive and depth-first and breadth-first
frontiers differ on live pending work.
-/

namespace Hex.Interval.NestedBranchConformance

open Experiment
open Propagator PolicySession SemanticReplay TargetRun BranchStart BranchTree
open ExpSign

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

private def splitAt (wanted : NodeId) (view : Policy.View Bound) :
    Option Policy.OfferView :=
  view.offers.toList.find? fun offer =>
    match offer.key with
    | .invoke invocation =>
        invocation.rule == splitRuleKey && invocation.anchor == wanted
    | .split _ seen _ _ => seen.node == wanted
    | _ => false

private def expAt (wanted : NodeId) (view : Policy.View Bound) :
    Option Policy.OfferView :=
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

private def resources : BranchTree.Limits :=
  { branch := { maxDepth := 3, maxScopes := 5 }
    maxSteps := 5
    maxSplits := 2
    maxLeaves := 3
    leafFuel := limits.policy.maxDecisions }

private def config (order : Order) : Config Bound Route :=
  { factDomain
    packages := splitPackages
    sessionLimits := limits
    controller
    splitter
    forkPolicy := fork
    order
    limits := resources }

private def run? (order : Order) (fuel : Nat) : Option (State Bound Route) := do
  let .ok state := BranchTree.start (config order) { index := 0 } input .root
    | none
  let .ok state := BranchTree.runFrom (config order) fuel state | none
  some state

private def leafReached? (entry : Node Bound Route) : Bool :=
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
    state.steps == 2 && state.splits == 2 && state.leaves == 3 &&
      state.frontier == [{ index := 3 }, { index := 4 }, { index := 2 }]

#guard
  (run? .breadthFirst 2).any fun state =>
    state.steps == 2 && state.splits == 2 && state.leaves == 3 &&
      state.frontier == [{ index := 2 }, { index := 3 }, { index := 4 }]

#guard
  (run? .depthFirst 5).any fun state =>
    state.settled && state.steps == 5 && state.splits == 2 &&
      state.leaves == 3 && state.nodes.size == 5 &&
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
    state.settled && state.steps == 5 && state.splits == 2 &&
      state.leaves == 3 && state.nodes.size == 5 &&
      state.nodes.toList.countP leafReached? == 3

end Hex.Interval.NestedBranchConformance
