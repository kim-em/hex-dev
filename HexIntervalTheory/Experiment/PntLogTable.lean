/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntLogTable
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Real semantics for the PNT+ logarithm-table probe

The Mathlib-free package propagates an opaque `logTwoWindow` fact.  This
companion interprets it as PNT+'s pinned six-decimal bounds and proves the
corresponding replay schema from Mathlib's stronger kernel-checked bounds.
No LeanCert definition or theorem is imported.
-/

namespace Hex.Interval.Experiment.PntLogTable

open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

/-- Mathematical meaning of the probe's finite facts. -/
def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .two, x => x = 2
  | .logTwoWindow, x => (0.693147 : ℝ) < x ∧ x < 0.693148
  | .empty, _ => False

def sourceModel : OperationSemantics.Model ℝ :=
  { operation := sourceOperation
    relation := fun inputs _ => inputs = [] }

def logModel : OperationSemantics.Model ℝ :=
  { operation := logOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = Real.log input
      | _ => False }

def operationModels : Array (OperationSemantics.Model ℝ) :=
  #[sourceModel, logModel]

def semantics : Semantics Bound :=
  OperationSemantics.semantics operationModels Contains

theorem containsMeet (left right : Bound) (x : ℝ) :
    Contains (left.meet right) x ↔ Contains left x ∧ Contains right x := by
  cases left <;> cases right <;> simp [Bound.meet, Contains]
  · intro equal _
    subst x
    norm_num
  · intro _ upper equal
    subst x
    norm_num at upper

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

/-- Semantic theorem for the package-owned table entry.  The watched input
fact is load-bearing: replay first recovers that the argument is exactly two,
then applies Mathlib's stronger decimal-nine theorems. -/
theorem logEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (inputFacts : assumptions = [{ node := input, fact := .two }]) :
    semantics.Entails graph assumptions
      { node := output, fact := .logTwoWindow } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .logTwoWindow (valuation output)
  intro valuation model holds
  have inputIsTwo : valuation input = 2 := by
    have exactInput := holds { node := input, fact := .two } (by simp [inputFacts])
    exact exactInput
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = Real.log (valuation input) := by
    simpa [logModel, arguments, List.map] using related
  rw [outputEq, inputIsTwo]
  constructor
  · exact (by
      have stronger := Real.log_two_gt_d9
      norm_num at stronger ⊢
      linarith)
  · exact (by
      have stronger := Real.log_two_lt_d9
      norm_num at stronger ⊢
      linarith)

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) :
    fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def logFactSchema : PackedFactSchema semantics where
  rule := logRuleKey
  schema := 1
  Certificate := Unit
  decode := fun body =>
    if body == [Bound.logTwoWindow.code] then some () else none
  replay := fun _ _ context _ =>
    if proposedFact : context.proposed.fact = .logTwoWindow then
      match found : context.program.node? context.proposed.node with
      | some instruction =>
          if operation : instruction.op = ({ index := 1 } : OpId) then
            match arguments : instruction.args with
            | [input] =>
                if inputFacts : context.assumptions =
                    [{ node := input, fact := .two }] then
                  some
                    { proof := by
                        have proposedEq :
                            context.proposed =
                              { node := context.proposed.node,
                                fact := .logTwoWindow } := by
                          exact factWith context.proposed proposedFact
                        rw [proposedEq]
                        exact
                          logEntails context.program context.assumptions
                            context.proposed.node instruction input found
                            operation arguments inputFacts }
                else
                  none
            | _ => none
          else
            none
      | none => none
    else
      none

def stableLaw : StableLaw semantics :=
  OperationSemantics.stableLaw operationModels Contains

def sourceEmit : EmitPackage Lean.Name := { schemas := [] }

def logEmit : EmitPackage Lean.Name :=
  { schemas :=
      [{ key := logFactSchema.key
         handle := ``logFactSchema }] }

def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }
    emit := sourceEmit }

def logProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[logFactSchema] }
    emit := logEmit }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, logProof]

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .two }, { node := node 1, fact := .all }]

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.two, .all]
    target := { node := node 1, fact := .logTwoWindow } }

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [program, node]

theorem basePrefix : ProgramPrefix program program :=
  ProgramPrefix.refl program

theorem sameOperations : program.operations = program.operations := rfl

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

noncomputable def valuation : NodeId → ℝ
  | ⟨0⟩ => 2
  | ⟨1⟩ => Real.log 2
  | _ => 0

theorem valuationModels : semantics.models program valuation := by
  refine ⟨?_, ?_⟩
  · simp [program, operations, operationModels, sourceModel, logModel]
  rintro ⟨index⟩ instruction found
  cases index with
  | zero =>
      simp [Program.node?, program, sourceInstruction] at found
      subst instruction
      exact ⟨sourceModel, by rfl, by rfl⟩
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, program, logInstruction] at found
          subst instruction
          exact ⟨logModel, by rfl, by rfl⟩
      | succ index =>
          simp [Program.node?, program] at found

/-- Close emitted generic evidence to the two ordinary PNT+ statements. -/
theorem closeLogTwo
    (result : Evidence
      (semantics.Entails program baseFacts checkerInput.target)) :
    (0.693147 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.693148 := by
  exact result.proof valuation valuationModels (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rfl
    · trivial)

end Hex.Interval.Experiment.PntLogTable
