/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntPiPoint
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Ordinary-kernel semantics for the PNT+ π point bound

The constant operation is interpreted as `Real.pi`. Its numerical theorem is
`Real.pi_lt_d2`, proved by Mathlib's nested-square-root/trigonometric bounds;
the Chudnovsky development is not imported.
-/

namespace Hex.Interval.Experiment.PntPiPoint

open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .request, x => x = 0
  | .upper cut, x => x < (cut.numerator : ℝ) / cut.denominator
  | .empty, _ => False

def sourceModel : Model ℝ :=
  { operation := sourceOperation, relation := fun inputs _ => inputs = [] }
def piModel : Model ℝ :=
  { operation := piOperation, relation := fun inputs output =>
      match inputs with | [input] => input = 0 ∧ output = Real.pi | _ => False }
def operationModels : Array (Model ℝ) := #[sourceModel, piModel]
def semantics : Semantics Bound := OperationSemantics.semantics operationModels Contains

def boundSchema : FactDomainSchema semantics where
  top := fun _ => .all
  topSound := by intros; trivial
  proveMeet := fun _ target previous proposed installed =>
    if same : previous = proposed then
      if exact : installed = previous then
        some
          { proof := by
              subst proposed
              subst installed
              intro valuation _
              change Contains previous (valuation target) ↔
                Contains previous (valuation target) ∧ Contains previous (valuation target)
              simp }
      else none
    else if rightTop : proposed = .all then
      if exact : installed = previous then
        some
          { proof := by
              subst proposed
              subst installed
              intro valuation _
              change Contains previous (valuation target) ↔
                Contains previous (valuation target) ∧ Contains .all (valuation target)
              simp [Contains] }
      else none
    else if leftTop : previous = .all then
      if exact : installed = proposed then
        some
          { proof := by
              subst previous
              subst installed
              intro valuation _
              change Contains proposed (valuation target) ↔
                Contains .all (valuation target) ∧ Contains proposed (valuation target)
              simp [Contains] }
      else none
    else none

def laws : Laws semantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change Contains fact (valuation left) ↔ Contains fact (valuation right)
      rw [values] }

theorem piEntails (value : Certificate) (accepted : value = certificate)
    (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (inputFacts : assumptions = [{ node := input, fact := .request }]) :
    semantics.Entails graph assumptions
      { node := output, fact := .upper value.cut } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  have inputZero : valuation input = 0 :=
    holds { node := input, fact := .request } (by simp [inputFacts])
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have relation : valuation input = 0 ∧ valuation output = Real.pi := by
    simpa [piModel, arguments, List.map] using related
  have outputEq := relation.2
  change valuation output < (value.cut.numerator : ℝ) / value.cut.denominator
  rw [outputEq, accepted]
  have bound := Real.pi_lt_d2
  norm_num [certificate, Certificate.cut] at bound ⊢
  exact bound

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) : fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def factSchema : PackedFactSchema semantics where
  rule := ruleKey
  schema := 1
  Certificate := Certificate
  decode := decode?
  replay := fun _ _ context value =>
    if accepted : value = certificate then
      if proposed : context.proposed.fact = .upper value.cut then
        match found : context.program.node? context.proposed.node with
        | some instruction =>
            if operation : instruction.op = ({ index := 1 } : OpId) then
              match arguments : instruction.args with
              | [input] =>
                  if inputFacts : context.assumptions =
                      [{ node := input, fact := .request }] then
                    some
                      { proof := by
                          rw [factWith context.proposed proposed]
                          exact piEntails value accepted context.program context.assumptions
                            context.proposed.node instruction input found operation arguments
                            inputFacts }
                  else none
              | _ => none
            else none
        | none => none
      else none
    else none

def stableLaw : StableLaw semantics := OperationSemantics.stableLaw operationModels Contains
def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }, emit := { schemas := [] } }
def piProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[factSchema] },
    emit := { schemas := [{ key := factSchema.key, handle := ``factSchema }] } }
def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) := #[sourceProof, piProof]

theorem pi_le_3_15 : Real.pi ≤ (3.15 : ℝ) := by
  have bound := Real.pi_lt_d2
  norm_num at bound ⊢
  exact bound.le

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .request }, { node := node 1, fact := .all }]
theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [program, node]
theorem basePrefix : ProgramPrefix program program := ProgramPrefix.refl program
theorem sameOperations : program.operations = program.operations := rfl
def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

noncomputable def valuation : NodeId → ℝ
  | ⟨0⟩ => 0
  | ⟨1⟩ => Real.pi
  | _ => 0

theorem valuationModels : semantics.models program valuation := by
  refine ⟨?_, ?_⟩
  · simp [program, operations, operationModels, sourceModel, piModel]
  rintro ⟨index⟩ instruction found
  cases index with
  | zero =>
      simp [Program.node?, program, sourceInstruction] at found
      subst instruction
      exact ⟨sourceModel, by rfl, by rfl⟩
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, program, piInstruction] at found
          subst instruction
          exact ⟨piModel, by rfl, by simp [piModel, valuation, node]⟩
      | succ index => simp [Program.node?, program] at found

theorem closePi
    (result : Evidence (semantics.Entails program baseFacts checkerInput.target)) :
    Real.pi < (3.15 : ℝ) := by
  have closed := result.proof valuation valuationModels (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rfl
    · trivial)
  change Contains (.upper certificate.cut) (valuation (node 1)) at closed
  norm_num [Contains, certificate, Certificate.cut, valuation, node] at closed ⊢
  exact closed

end Hex.Interval.Experiment.PntPiPoint
