/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.GenericInstanceReconstruction

@[expose] public section

/-!
# Package-composed operation semantics

This experiment interprets an expression program without a central switch on
operation keys. Each package contributes its opaque operation signature and a
relation between argument values and the result value. A program model must
find the relation at every referenced operation index; missing meanings do not
make a node unconstrained.
-/

namespace Hex.Interval.Experiment.OperationSemantics

open Propagator SemanticReplay ChronologicalReplay
open GenericInstanceReconstruction

/-- The mathematical meaning contributed by one operation package. -/
structure Model (Value : Type) where
  operation : Operation
  relation : List Value → Value → Prop

/-- Pointwise alignment between semantic models and opaque operations. -/
def Aligned : List (Model Value) → List Operation → Prop
  | [], [] => True
  | model :: models, operation :: operations =>
      model.operation = operation ∧ Aligned models operations
  | _, _ => False

theorem Aligned.map {models : List (Model Value)} {operations : List Operation}
    (aligned : Aligned models operations) :
    models.map (fun model => model.operation) = operations := by
  induction models generalizing operations with
  | nil => cases operations <;> simp_all [Aligned]
  | cons model models ih =>
      cases operations with
      | nil => simp [Aligned] at aligned
      | cons operation operations =>
          simp only [Aligned] at aligned
          simp [aligned.1, ih aligned.2]

/-- Exact array equality follows from package-by-package operation alignment. -/
theorem operationsOfAligned (models : Array (Model Value))
    (operations : Array Operation)
    (aligned : Aligned models.toList operations.toList) :
    operations = models.map (fun model => model.operation) := by
  apply Array.toList_inj.mp
  simpa using aligned.map.symm

/-- Every operation and node in a program is interpreted by the aligned model
array. The exact operation-array equality prevents a meaning from being paired
with a different opaque operation signature. -/
def Models (models : Array (Model Value)) (program : Program)
    (valuation : NodeId → Value) : Prop :=
  program.operations = models.map (fun model => model.operation) ∧
    ∀ node instruction, program.node? node = some instruction →
      ∃ model,
        models[instruction.op.index]? = some model ∧
          model.relation (instruction.args.map valuation) (valuation node)

/-- The meaning of one instruction at its exact SSA node. -/
def NodeMeaning (models : Array (Model Value)) (valuation : NodeId → Value)
    (node : NodeId) (instruction : Node) : Prop :=
  ∃ model,
    models[instruction.op.index]? = some model ∧
      model.relation (instruction.args.map valuation) (valuation node)

/-- Node meanings in exact program order.  This proposition is deliberately
list-shaped so a tactic can emit one package-owned relation proof per reified
node and combine them without a switch on operation keys. -/
def Meanings (models : Array (Model Value)) (valuation : NodeId → Value) :
    Nat → List Node → Prop
  | _, [] => True
  | index, instruction :: rest =>
      NodeMeaning models valuation { index } instruction ∧
        Meanings models valuation (index + 1) rest

theorem Meanings.at {models : Array (Model Value)}
    {valuation : NodeId → Value} {start : Nat} {nodes : List Node}
    (meanings : Meanings models valuation start nodes) (offset : Nat)
    {instruction : Node} (found : nodes[offset]? = some instruction) :
    NodeMeaning models valuation { index := start + offset } instruction := by
  induction nodes generalizing start offset with
  | nil => simp at found
  | cons head tail ih =>
      cases offset with
      | zero =>
          simp at found
          subst head
          simpa [Meanings] using meanings.1
      | succ offset =>
          simp at found
          have tailMeaning := ih meanings.2 offset found
          have indices : (start + 1) + offset = start + (offset + 1) := by
            omega
          simpa [indices] using tailMeaning

/-- Assemble the global program model from the exact operation alignment and
one relation proof for every node. -/
theorem modelsOfMeanings (models : Array (Model Value)) (program : Program)
    (valuation : NodeId → Value)
    (operations : program.operations = models.map (fun model => model.operation))
    (meanings : Meanings models valuation 0 program.nodes.toList) :
    Models models program valuation := by
  refine ⟨operations, ?_⟩
  intro node instruction found
  have foundList : program.nodes.toList[node.index]? = some instruction := by
    simpa [Program.node?] using found
  simpa [NodeMeaning] using meanings.at node.index foundList

/-- Node-local fact semantics over a package-composed operation model. -/
def semantics (models : Array (Model Value))
    (Contains : Fact → Value → Prop) : Semantics Fact :=
  { Value
    models := Models models
    holds := fun _ valuation fact => Contains fact.fact (valuation fact.node) }

theorem nodeAt {before after : Program}
    (step : ProgramPrefix before after) (node : NodeId)
    (instruction : Node) (found : before.node? node = some instruction) :
    after.node? node = some instruction := by
  have within : node.index < before.nodes.size := by
    by_cases inside : node.index < before.nodes.size
    · exact inside
    · simp [Program.node?, inside] at found
  rw [Program.node?, step.nodeAt node.index within]
  exact found

/-- Node-local meanings satisfy one uniform append-only stability law. -/
def stableLaw (models : Array (Model Value))
    (Contains : Fact → Value → Prop) :
    StableLaw (semantics models Contains) :=
  { stable := by
      intro before after _ _ step sameOperations
      refine
        { programPrefix := step
          modelsBefore := ?_
          holdsOld := ?_ }
      · intro valuation model
        refine ⟨sameOperations.trans model.1, ?_⟩
        intro node instruction found
        exact model.2 node instruction (nodeAt step node instruction found)
      · intro oldValue newValue fact within _ _ agreement
        change Contains fact.fact (oldValue fact.node) ↔
          Contains fact.fact (newValue fact.node)
        rw [agreement fact.node within] }

end Hex.Interval.Experiment.OperationSemantics
