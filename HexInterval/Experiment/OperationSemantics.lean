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

/-- Node-local meanings admit one uniform append-only stability law. -/
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
        rw [agreement] }

end Hex.Interval.Experiment.OperationSemantics
