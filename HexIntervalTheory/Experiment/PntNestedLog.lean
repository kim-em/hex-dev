/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntNestedLog
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

namespace Hex.Interval.Experiment.PntNestedLog

open Finset

private theorem logSix58Window :
    (1.884034 : ℝ) < Real.log 6.58 ∧ Real.log 6.58 < 1.884035 := by
  have habs : |(279 : ℝ) / 329| = (279 : ℝ) / 329 := by norm_num
  have remainder := Real.abs_log_sub_add_sum_range_le
    (x := (279 : ℝ) / 329) (by norm_num) 150
  rw [habs, show (1 : ℝ) - 279 / 329 = 50 / 329 by norm_num,
    show (50 : ℝ) / 329 = ((329 : ℝ) / 50)⁻¹ by norm_num,
    Real.log_inv, ← sub_eq_add_neg, abs_sub_comm] at remainder
  rw [abs_le] at remainder
  constructor <;> norm_num [sum_range_succ] at remainder ⊢ <;> linarith

private theorem logInnerLower :
    (0.633415 : ℝ) < Real.log 1.884034 := by
  have habs : |(442017 : ℝ) / 942017| = (442017 : ℝ) / 942017 := by norm_num
  have remainder := Real.abs_log_sub_add_sum_range_le
    (x := (442017 : ℝ) / 942017) (by norm_num) 40
  rw [habs, show (1 : ℝ) - 442017 / 942017 = 500000 / 942017 by norm_num,
    show (500000 : ℝ) / 942017 = ((942017 : ℝ) / 500000)⁻¹ by norm_num,
    Real.log_inv, ← sub_eq_add_neg, abs_sub_comm] at remainder
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  linarith

open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

/-- Mathematical meaning of the package-owned rational point and interval
facts. -/
def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .six58, x => x = 329 / 50
  | .innerWindow, x => (1.884034 : ℝ) < x ∧ x < 1.884035
  | .zeroTouchingInner, x => (0 : ℝ) ≤ x ∧ x < 1.884035
  | .nestedLower, x => (0.633415 : ℝ) < x
  | .positiveSlice, x => (0.633415 : ℝ) < x ∧ x < 1.884035
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
  cases left <;> cases right <;>
    simp [Bound.meet, Contains] <;> norm_num <;>
    aesop (config := { warnOnNonterminal := false }) <;>
    norm_num at * <;> linarith

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

private theorem operationOutput
    (graph : Program) (valuation : NodeId → ℝ)
    (model : OperationSemantics.Models operationModels graph valuation)
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input]) :
    valuation output = Real.log (valuation input) := by
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  simpa [logModel, arguments, List.map] using related

/-- First replay stage: the exact rational point produces a strict positive
enclosure for its logarithm. -/
theorem innerEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (inputFacts : assumptions = [{ node := input, fact := .six58 }]) :
    semantics.Entails graph assumptions
      { node := output, fact := .innerWindow } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .innerWindow (valuation output)
  intro valuation model holds
  have inputExact : valuation input = 329 / 50 := by
    exact holds { node := input, fact := .six58 } (by simp [inputFacts])
  have outputEq := operationOutput graph valuation model output instruction input
    found operation arguments
  change (1.884034 : ℝ) < valuation output ∧ valuation output < 1.884035
  rw [outputEq, inputExact]
  rw [show (329 / 50 : ℝ) = 6.58 by norm_num]
  exact logSix58Window

/-- Second replay stage: the strict lower endpoint of the inner enclosure is
load-bearing.  Monotonicity transfers an independently checked point bound to
the actual inner logarithm. -/
theorem outerEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (inputFacts : assumptions = [{ node := input, fact := .innerWindow }]) :
    semantics.Entails graph assumptions
      { node := output, fact := .nestedLower } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .nestedLower (valuation output)
  intro valuation model holds
  have inner := holds { node := input, fact := .innerWindow } (by simp [inputFacts])
  have inputPositive : 0 < valuation input := lt_trans (by norm_num) inner.1
  have outputEq := operationOutput graph valuation model output instruction input
    found operation arguments
  change (0.633415 : ℝ) < valuation output
  rw [outputEq]
  exact logInnerLower.trans
    ((Real.log_lt_log_iff (by norm_num) inputPositive).2 inner.1)

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) :
    fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def logFactSchema : PackedFactSchema semantics where
  rule := logRuleKey
  schema := 1
  Certificate := Bound
  decode := fun body =>
    match body with
    | [code] =>
        match Bound.ofCode? code with
        | some .innerWindow => some .innerWindow
        | some .nestedLower => some .nestedLower
        | _ => none
    | _ => none
  replay := fun _ _ context certificate =>
    match found : context.program.node? context.proposed.node with
    | some instruction =>
        if operation : instruction.op = ({ index := 1 } : OpId) then
          match arguments : instruction.args with
          | [input] =>
              match certificate with
              | .innerWindow =>
                  if proposedFact : context.proposed.fact = .innerWindow then
                    if inputFacts : context.assumptions =
                        [{ node := input, fact := .six58 }] then
                      some
                        { proof := by
                            rw [factWith context.proposed proposedFact]
                            exact innerEntails context.program context.assumptions
                              context.proposed.node instruction input found
                              operation arguments inputFacts }
                    else none
                  else none
              | .nestedLower =>
                  if proposedFact : context.proposed.fact = .nestedLower then
                    if inputFacts : context.assumptions =
                        [{ node := input, fact := .innerWindow }] then
                      some
                        { proof := by
                            rw [factWith context.proposed proposedFact]
                            exact outerEntails context.program context.assumptions
                              context.proposed.node instruction input found
                              operation arguments inputFacts }
                    else none
                  else none
              | _ => none
          | _ => none
        else none
    | none => none

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
  [{ node := node 0, fact := .six58 },
    { node := node 1, fact := .all },
    { node := node 2, fact := .all }]

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.six58, .all, .all]
    target := { node := node 2, fact := .nestedLower } }

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [program, node]

theorem basePrefix : ProgramPrefix program program :=
  ProgramPrefix.refl program

theorem sameOperations : program.operations = program.operations := rfl

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

noncomputable def valuation : NodeId → ℝ
  | ⟨0⟩ => 329 / 50
  | ⟨1⟩ => Real.log (329 / 50)
  | ⟨2⟩ => Real.log (Real.log (329 / 50))
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
          simp [Program.node?, program, innerInstruction] at found
          subst instruction
          exact ⟨logModel, by rfl, by rfl⟩
      | succ index =>
          cases index with
          | zero =>
              simp [Program.node?, program, outerInstruction] at found
              subst instruction
              exact ⟨logModel, by rfl, by rfl⟩
          | succ index =>
              simp [Program.node?, program] at found

/-- Close emitted generic evidence to the pinned ordinary PNT+ theorem. -/
theorem closeNestedLog
    (result : Evidence
      (semantics.Entails program baseFacts checkerInput.target)) :
    (0.633415 : ℝ) < Real.log (Real.log 6.58) := by
  have closed := result.proof valuation valuationModels (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rfl
    · trivial
    · trivial)
  change (0.633415 : ℝ) < Real.log (Real.log (329 / 50)) at closed
  norm_num at closed ⊢
  exact closed

end Hex.Interval.Experiment.PntNestedLog
