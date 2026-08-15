/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Search
public import Mathlib

@[expose] public section

/-!
# Function-agnostic program semantics

This module is the supported Mathlib proof interpretation of a checked
`Hex.Interval.Program`. Each package contributes one exact operation signature
and a relation on argument and result values. `Program.Models` requires the
meaning array to align exactly with the opaque operation array and requires a
relation witness at every SSA node. Missing or reordered meanings do not leave
nodes unconstrained.
-/

namespace Hex.Interval.Program

/-- Mathematical meaning of one exact opaque operation signature. -/
structure Meaning (Value : Type) where
  operation : Operation
  relation : List Value → Value → Prop

/-- Package meanings align pointwise with the supported operation snapshot. -/
def Aligned : List (Meaning Value) → List Operation → Prop
  | [], [] => True
  | meaning :: meanings, operation :: operations =>
      meaning.operation = operation ∧ Aligned meanings operations
  | _, _ => False

theorem Aligned.map {meanings : List (Meaning Value)} {operations : List Operation}
    (aligned : Aligned meanings operations) :
    meanings.map (·.operation) = operations := by
  induction meanings generalizing operations with
  | nil => cases operations <;> simp_all [Aligned]
  | cons meaning meanings ih =>
      cases operations with
      | nil => simp [Aligned] at aligned
      | cons operation operations =>
          simp only [Aligned] at aligned
          simp [aligned.1, ih aligned.2]

/-- Exact operation-array equality follows from package-by-package alignment. -/
theorem operationsOfAligned (meanings : Array (Meaning Value))
    (operations : Array Operation)
    (aligned : Aligned meanings.toList operations.toList) :
    operations = meanings.map (·.operation) := by
  apply Array.toList_inj.mp
  simpa using aligned.map.symm

/-- Meaning of one instruction at its exact SSA node. -/
def MeaningAt (meanings : Array (Meaning Value)) (valuation : NodeId → Value)
    (node : NodeId) (instruction : Node) : Prop :=
  ∃ meaning,
    meanings[instruction.op.index]? = some meaning ∧
      meaning.relation (instruction.args.map valuation) (valuation node)

/-- Every operation and node has its exact aligned package meaning. -/
def Models (meanings : Array (Meaning Value)) (program : Program)
    (valuation : NodeId → Value) : Prop :=
  program.operations = meanings.map (·.operation) ∧
    ∀ node instruction, program.node? node = some instruction →
      MeaningAt meanings valuation node instruction

/-- Node meanings in exact program order, convenient for proof emission. -/
def Meanings (meanings : Array (Meaning Value)) (valuation : NodeId → Value) :
    Nat → List Node → Prop
  | _, [] => True
  | index, instruction :: rest =>
      MeaningAt meanings valuation { index } instruction ∧
        Meanings meanings valuation (index + 1) rest

theorem Meanings.at {meanings : Array (Meaning Value)}
    {valuation : NodeId → Value} {start : Nat} {nodes : List Node}
    (proofs : Meanings meanings valuation start nodes) (offset : Nat)
    {instruction : Node} (found : nodes[offset]? = some instruction) :
    MeaningAt meanings valuation { index := start + offset } instruction := by
  induction nodes generalizing start offset with
  | nil => simp at found
  | cons head tail ih =>
      cases offset with
      | zero =>
          simp at found
          subst head
          simpa [Meanings] using proofs.1
      | succ offset =>
          simp at found
          have tailProof := ih proofs.2 offset found
          have indices : (start + 1) + offset = start + (offset + 1) := by omega
          simpa [indices] using tailProof

/-- Assemble the global model from exact operation alignment and one relation
proof per node. -/
theorem modelsOfMeanings (meanings : Array (Meaning Value)) (program : Program)
    (valuation : NodeId → Value)
    (operations : program.operations = meanings.map (·.operation))
    (proofs : Meanings meanings valuation 0 program.nodes.toList) :
    Models meanings program valuation := by
  refine ⟨operations, ?_⟩
  intro node instruction found
  have foundList : program.nodes.toList[node.index]? = some instruction := by
    simpa [Program.node?] using found
  simpa [MeaningAt] using proofs.at node.index foundList

end Hex.Interval.Program
