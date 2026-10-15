/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntNestedLogTwo
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Ordinary-kernel semantics for two-sided `log (log 2)`

The first replay event checks the strict positive decimal-nine enclosure for
`log 2`. The second event uses both endpoints, two independent fourteen-term
Taylor remainder checks, and logarithm monotonicity to enclose the outer log.
-/

namespace Hex.Interval.Experiment.PntNestedLogTwo

open Finset
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

private theorem outerLowerPoint :
    (-0.366513 : ℝ) < Real.log (0.6931471803 : ℝ) := by
  have habs : |(3068528197 : ℝ) / 10000000000| =
      (3068528197 : ℝ) / 10000000000 := by norm_num
  have remainder := Real.abs_log_sub_add_sum_range_le
    (x := (3068528197 : ℝ) / 10000000000) (by norm_num) 14
  rw [habs, show (1 : ℝ) - 3068528197 / 10000000000 =
    6931471803 / 10000000000 by norm_num] at remainder
  rw [abs_le] at remainder
  norm_num [Finset.sum_range_succ] at remainder ⊢
  linarith

private theorem outerUpperPoint :
    Real.log (0.6931471808 : ℝ) < -0.366512 := by
  have habs : |(3068528192 : ℝ) / 10000000000| =
      (3068528192 : ℝ) / 10000000000 := by norm_num
  have remainder := Real.abs_log_sub_add_sum_range_le
    (x := (3068528192 : ℝ) / 10000000000) (by norm_num) 14
  rw [habs, show (1 : ℝ) - 3068528192 / 10000000000 =
    6931471808 / 10000000000 by norm_num] at remainder
  rw [abs_le] at remainder
  norm_num [Finset.sum_range_succ] at remainder ⊢
  linarith

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .two, x => x = 2
  | .innerWindow, x => (0.6931471803 : ℝ) < x ∧ x < 0.6931471808
  | .zeroTouchingInner, x => (0 : ℝ) ≤ x ∧ x < 0.6931471808
  | .outerWindow, x => (-0.366513 : ℝ) < x ∧ x < -0.366512
  | .empty, _ => False

def sourceModel : Model ℝ :=
  { operation := sourceOperation, relation := fun inputs _ => inputs = [] }
def logModel : Model ℝ :=
  { operation := logOperation, relation := fun inputs output =>
      match inputs with | [input] => output = Real.log input | _ => False }
def operationModels : Array (Model ℝ) := #[sourceModel, logModel]
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

private theorem operationOutput (graph : Program) (valuation : NodeId → ℝ)
    (model : Models operationModels graph valuation)
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input]) :
    valuation output = Real.log (valuation input) := by
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  simpa [logModel, arguments, List.map] using related

theorem innerEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (inputFacts : assumptions = [{ node := input, fact := .two }]) :
    semantics.Entails graph assumptions { node := output, fact := .innerWindow } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  have inputTwo : valuation input = 2 :=
    holds { node := input, fact := .two } (by simp [inputFacts])
  have outputEq := operationOutput graph valuation model output instruction input
    found operation arguments
  change Contains .innerWindow (valuation output)
  rw [outputEq, inputTwo]
  exact ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

theorem outerEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (inputFacts : assumptions = [{ node := input, fact := .innerWindow }]) :
    semantics.Entails graph assumptions { node := output, fact := .outerWindow } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  have inner := holds { node := input, fact := .innerWindow } (by simp [inputFacts])
  have inputPositive : 0 < valuation input := lt_trans (by norm_num) inner.1
  have outputEq := operationOutput graph valuation model output instruction input
    found operation arguments
  change Contains .outerWindow (valuation output)
  rw [outputEq]
  constructor
  · exact outerLowerPoint.trans
      ((Real.log_lt_log_iff (by norm_num) inputPositive).2 inner.1)
  · exact ((Real.log_lt_log_iff inputPositive (by norm_num)).2 inner.2).trans
      outerUpperPoint

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) : fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def factSchema : PackedFactSchema semantics where
  rule := ruleKey
  schema := 1
  Certificate := Bound
  decode := fun body => match body with
    | [code] => match Bound.ofCode? code with
      | some .innerWindow => some .innerWindow
      | some .outerWindow => some .outerWindow
      | _ => none
    | _ => none
  replay := fun _ _ context certificate =>
    match found : context.program.node? context.proposed.node with
    | some instruction =>
        if operation : instruction.op = ({ index := 1 } : OpId) then
          match arguments : instruction.args with
          | [input] => match certificate with
            | .innerWindow =>
                if proposed : context.proposed.fact = .innerWindow then
                  if inputFacts : context.assumptions =
                      [{ node := input, fact := .two }] then
                    some
                      { proof := by
                          rw [factWith context.proposed proposed]
                          exact innerEntails context.program context.assumptions
                            context.proposed.node instruction input found operation arguments
                            inputFacts }
                  else none
                else none
            | .outerWindow =>
                if proposed : context.proposed.fact = .outerWindow then
                  if inputFacts : context.assumptions =
                      [{ node := input, fact := .innerWindow }] then
                    some
                      { proof := by
                          rw [factWith context.proposed proposed]
                          exact outerEntails context.program context.assumptions
                            context.proposed.node instruction input found operation arguments
                            inputFacts }
                  else none
                else none
            | _ => none
          | _ => none
        else none
    | none => none

def stableLaw : StableLaw semantics := OperationSemantics.stableLaw operationModels Contains
def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }, emit := { schemas := [] } }
def logProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[factSchema] },
    emit := { schemas := [{ key := factSchema.key, handle := ``factSchema }] } }
def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) := #[sourceProof, logProof]

theorem log_log_2_gt : (-0.366513 : ℝ) ≤ Real.log (Real.log 2) := by
  have innerPositive : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (outerLowerPoint.trans
    ((Real.log_lt_log_iff (by norm_num) innerPositive).2 Real.log_two_gt_d9)).le

theorem log_log_2_lt : Real.log (Real.log 2) ≤ -0.366512 := by
  have innerPositive : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (((Real.log_lt_log_iff innerPositive (by norm_num)).2
    Real.log_two_lt_d9).trans outerUpperPoint).le

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .two }, { node := node 1, fact := .all },
   { node := node 2, fact := .all }]

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [program, node]

theorem basePrefix : ProgramPrefix program program := ProgramPrefix.refl program
theorem sameOperations : program.operations = program.operations := rfl
def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

noncomputable def valuation : NodeId → ℝ
  | ⟨0⟩ => 2
  | ⟨1⟩ => Real.log 2
  | ⟨2⟩ => Real.log (Real.log 2)
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
          | succ index => simp [Program.node?, program] at found

theorem closeNestedLogTwo
    (result : Evidence (semantics.Entails program baseFacts checkerInput.target)) :
    (-0.366513 : ℝ) < Real.log (Real.log 2) ∧
      Real.log (Real.log 2) < -0.366512 := by
  exact result.proof valuation valuationModels (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rfl
    · trivial
    · trivial)

end Hex.Interval.Experiment.PntNestedLogTwo
