/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.BranchTree
public import HexInterval.Experiment.ProofFrontend

@[expose] public section

/-!
# Generic branch-tree proof emission

This frontend folds a settled retained branch tree from its leaves to its root.
It knows no fact representation, mathematical function, proof schema, or
branch policy.  Client callbacks replay an exact closed leaf and join an exact
split; the generic fold validates tree shape, total coverage, and the final
Lean type.

Runtime tree data remains untrusted.  Every callback result is an ordinary
`Expr`, and later callback applications plus the final type check force the
kernel-facing theorem structure.  Pending, blocked, failed, unreachable,
duplicated, or cyclic nodes are rejected before a root term is returned.
-/

namespace Hex.Interval.Experiment.BranchProof

open Lean Meta
open BranchTree

/-- Structural traversal resources, independent of search resources already
charged by `BranchTree`. -/
structure Limits where
  maxNodes : Nat
  maxDepth : Nat
  deriving DecidableEq, Repr

/-- Proof-producing operations for one semantics adapter and package set. -/
structure Emitter (Fact PolicyState : Type) where
  leaf : BranchTree.Leaf Fact PolicyState ->
    TargetRun.Result Fact PolicyState -> MetaM Expr
  split : BranchTree.Leaf Fact PolicyState ->
    TargetRun.Result Fact PolicyState -> BranchStart.Children Fact ->
    Expr -> Expr -> MetaM Expr

structure Output (Fact PolicyState : Type) where
  proof : Expr
  seen : List Nat
  source : BranchTree.Leaf Fact PolicyState

def overlap (left right : List Nat) : Bool :=
  left.any right.contains

def sameInput [DecidableEq Fact]
    (left right : SemanticReplay.CheckerInput Fact) : Bool :=
  left.baseProgram == right.baseProgram &&
    left.initialFacts == right.initialFacts && left.target == right.target

/-- The split parent is the completed run's current snapshot, not necessarily
its starting input: propagation and instantiation may precede subdivision. -/
def sameParent [DecidableEq Fact] (source : BranchTree.Leaf Fact PolicyState)
    (run : TargetRun.Result Fact PolicyState)
    (parent : SemanticReplay.CheckerInput Fact) : Bool :=
  parent.baseProgram == run.session.state.engine.program &&
    parent.initialFacts == run.session.state.engine.facts &&
    parent.target == source.input.target

def samePlan [DecidableEq Fact] (left right : Propagator.Policy.SplitPlan Fact) : Bool :=
  left.scope == right.scope && left.suggestion == right.suggestion &&
    left.origin == right.origin && left.node == right.node &&
    left.version == right.version && left.fact == right.fact &&
    left.point == right.point && left.reason == right.reason &&
    left.source == right.source

def sameChild [DecidableEq Fact]
    (scope : Propagator.Policy.ScopeId) (depth : Nat)
    (input : SemanticReplay.CheckerInput Fact)
    (source : BranchTree.Leaf Fact PolicyState) : Bool :=
  source.scope == scope && source.depth == depth && sameInput source.input input

partial def emitAt [DecidableEq Fact]
    (limits : Limits) (emitter : Emitter Fact PolicyState)
    (tree : BranchTree.State Fact PolicyState) (depth : Nat)
    (id : BranchTree.TreeId) : MetaM (Output Fact PolicyState) := do
  if depth > limits.maxDepth then
    throwError "interval branch proof: traversal depth exhausted"
  let some node := tree.nodes[id.index]?
    | throwError "interval branch proof: missing node {id.index}"
  match node with
  | .pending _ =>
      throwError "interval branch proof: pending node {id.index} is not closed"
  | .leaf source ending =>
      match ending with
      | .result run =>
          unless BranchStart.sameInput source.scope source.input run do
            throwError "interval branch proof: leaf input does not match its run"
          pure
            { proof := ← emitter.leaf source run
              seen := [id.index]
              source }
      | .blocked _ _ =>
          throwError "interval branch proof: blocked node {id.index} is not closed"
      | .startError _ =>
          throwError "interval branch proof: failed node {id.index} is not closed"
  | .split source run children left right =>
      if left.index <= id.index || right.index <= id.index then
        throwError "interval branch proof: child does not follow its parent"
      if left.index == right.index then
        throwError "interval branch proof: split reuses one child"
      let leftOutput ← emitAt limits emitter tree (depth + 1) left
      let rightOutput ← emitAt limits emitter tree (depth + 1) right
      unless BranchStart.sameInput source.scope source.input run do
        throwError "interval branch proof: split input does not match its run"
      unless sameParent source run children.parent do
        throwError "interval branch proof: split parent is not the run's current state"
      match run.stop with
      | .split plan =>
          unless samePlan plan children.plan do
            throwError "interval branch proof: split plan changed"
      | _ =>
          throwError "interval branch proof: retained split did not stop at a split"
      unless sameChild children.leftScope children.depth children.left
          leftOutput.source do
        throwError "interval branch proof: left child input changed"
      unless sameChild children.rightScope children.depth children.right
          rightOutput.source do
        throwError "interval branch proof: right child input changed"
      if overlap leftOutput.seen rightOutput.seen then
        throwError "interval branch proof: subtrees share a node"
      let proof ← emitter.split source run children
        leftOutput.proof rightOutput.proof
      pure
        { proof
          seen := id.index :: (leftOutput.seen ++ rightOutput.seen)
          source }

/-- Emit one root theorem only from a settled, totally covered tree.

`expected` is normally the current goal type.  The final check is deliberately
inside the generic frontend, so even a single-leaf tree cannot return an
unrelated callback term. -/
def emit [DecidableEq Fact] (limits : Limits) (emitter : Emitter Fact PolicyState)
    (tree : BranchTree.State Fact PolicyState) (expected : Expr) : MetaM Expr := do
  if !tree.frontier.isEmpty then
    throwError "interval branch proof: tree still has pending work"
  if tree.nodes.isEmpty then
    throwError "interval branch proof: tree has no root"
  if tree.nodes.size > limits.maxNodes then
    throwError "interval branch proof: node budget exhausted"
  let output ← emitAt limits emitter tree 0 { index := 0 }
  if output.seen.length != tree.nodes.size then
    throwError "interval branch proof: tree contains unreachable nodes"
  let proof ← instantiateMVars output.proof
  unless ← isDefEq (← inferType proof) expected do
    throwError "interval branch proof: emitted root has the wrong type"
  pure proof

end Hex.Interval.Experiment.BranchProof
