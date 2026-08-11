/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import HexInterval.Experiment.ExpSign
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Real semantics for exponential-sign propagation

This companion interprets the independent Mathlib-free exponential package
over `ℝ` and contributes its semantic replay theorem and frontend handle.
-/

namespace Hex.Interval.Experiment.ExpSign

open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .nonnegative, x => 0 ≤ x
  | .empty, _ => False

def sourceModel : OperationSemantics.Model ℝ :=
  { operation := sourceOperation
    relation := fun inputs _ => inputs = [] }

def expModel : OperationSemantics.Model ℝ :=
  { operation := expOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = Real.exp input
      | _ => False }

def operationModels : Array (OperationSemantics.Model ℝ) :=
  #[sourceModel, expModel]

def semantics : Semantics Bound :=
  OperationSemantics.semantics operationModels Contains

theorem containsMeet (left right : Bound) (x : ℝ) :
    Contains (left.meet right) x ↔ Contains left x ∧ Contains right x := by
  cases left <;> cases right <;>
    simp_all [Bound.meet, Contains]

def boundSchema : FactDomainSchema semantics :=
  { top := fun _ => .all
    topSound := by
      intro _ _ _ _ _ _
      trivial
    proveMeet := fun _ _ previous proposed installed =>
      if exact : installed = previous.meet proposed then
        some
          { proof := by
              subst installed
              intro valuation _
              exact containsMeet previous proposed (valuation _) }
      else
        none }

def laws : Laws semantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change Contains fact (valuation left) ↔ Contains fact (valuation right)
      rw [values] }

theorem expEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input]) :
    semantics.Entails graph assumptions
      { node := output, fact := .nonnegative } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .nonnegative (valuation output)
  intro valuation model _
  obtain ⟨meaning, meaningAt, related⟩ :=
    model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = Real.exp (valuation input) := by
    simpa [expModel, arguments, List.map] using related
  change (0 : ℝ) ≤ valuation output
  rw [outputEq]
  exact (Real.exp_pos _).le

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) :
    fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def expFactSchema : PackedFactSchema semantics where
  rule := expRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body =>
    if body == [Bound.nonnegative.code] then some () else none
  replay := fun _ _ context _ =>
    if proposedFact : context.proposed.fact = .nonnegative then
      match found : context.program.node? context.proposed.node with
      | some instruction =>
          if operation : instruction.op = ({ index := 1 } : OpId) then
            match arguments : instruction.args with
            | [input] =>
                some
                  { proof := by
                      have proposedEq :
                          context.proposed =
                            { node := context.proposed.node,
                              fact := .nonnegative } := by
                        exact factWith context.proposed proposedFact
                      rw [proposedEq]
                      exact
                        expEntails context.program context.assumptions
                          context.proposed.node instruction input found
                          operation arguments }
            | _ => none
          else
            none
      | none => none
    else
      none

def stableLaw : StableLaw semantics :=
  OperationSemantics.stableLaw operationModels Contains

def sourceEmit : EmitPackage Lean.Name := { schemas := [] }

def expEmit : EmitPackage Lean.Name :=
  { schemas :=
      [{ key := expFactSchema.key
         handle := ``expFactSchema }] }

def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }
    emit := sourceEmit }

def expProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[expFactSchema] }
    emit := expEmit }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, expProof]

def semanticPackages : Array (SemanticReplay.Package semantics) :=
  proofPackages.map (fun package => package.semantic)

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .all }, { node := node 1, fact := .all }]

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.all, .all]
    target := { node := node 1, fact := .nonnegative } }

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [program, node]

theorem basePrefix : ProgramPrefix program program :=
  ProgramPrefix.refl program

theorem sameOperations : program.operations = program.operations := rfl

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

noncomputable def valuation (x : ℝ) : NodeId → ℝ
  | ⟨0⟩ => x
  | ⟨1⟩ => Real.exp x
  | _ => 0

theorem valuationModels (x : ℝ) : semantics.models program (valuation x) := by
  refine ⟨?_, ?_⟩
  · simp [program, operations, operationModels, sourceModel, expModel]
  rintro ⟨index⟩ instruction found
  cases index with
  | zero =>
      simp [Program.node?, program, sourceInstruction] at found
      subst instruction
      exact ⟨sourceModel, by rfl, by rfl⟩
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, program, expInstruction] at found
          subst instruction
          exact ⟨expModel, by rfl, by rfl⟩
      | succ index =>
          simp [Program.node?, program] at found

/-- Turn the generic emitted evidence into the ordinary user theorem. -/
theorem closeExp (x : ℝ)
    (result : Evidence
      (semantics.Entails program baseFacts checkerInput.target)) :
    0 ≤ Real.exp x := by
  have holds := result.proof (valuation x) (valuationModels x)
    (by
      intro fact member
      simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> trivial)
  exact holds

end Hex.Interval.Experiment.ExpSign
