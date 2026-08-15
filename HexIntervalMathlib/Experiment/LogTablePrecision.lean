/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.LogTablePrecision
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.LogTablePrecision

open Finset
open Hex.Interval.Experiment
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics
open Hex.Interval.Experiment.LogTablePrecision

noncomputable def partialSum (terms : Nat) : ℝ :=
  ∑ k ∈ range terms,
    2 * (1 / (2 * (k : ℝ) + 1)) * (1 / 3 : ℝ) ^ (2 * k + 1)

noncomputable def tailBound (terms : Nat) : ℝ :=
  2 * (1 / 3 : ℝ) ^ (2 * terms + 1) / (1 - (1 / 3 : ℝ) ^ 2)

theorem partialSum_le_logTwo (terms : Nat) :
    partialSum terms ≤ Real.log 2 := by
  have bound := Real.sum_range_le_log_div (x := (1 / 3 : ℝ)) (by norm_num)
    (by norm_num) terms
  have scaled := mul_le_mul_of_nonneg_left bound (by norm_num : (0 : ℝ) ≤ 2)
  calc
    partialSum terms =
        2 * ∑ k ∈ range terms,
          (1 / 3 : ℝ) ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
      simp only [partialSum, mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ 2 * (1 / 2 * Real.log ((1 + (1 / 3 : ℝ)) / (1 - 1 / 3))) := scaled
    _ = Real.log 2 := by
      norm_num
      ring

theorem logTwo_le_partialSum_add_tailBound (terms : Nat) :
    Real.log 2 ≤ partialSum terms + tailBound terms := by
  have bound := Real.log_div_le_sum_range_add (x := (1 / 3 : ℝ)) (by norm_num)
    (by norm_num) terms
  have scaled := mul_le_mul_of_nonneg_left bound (by norm_num : (0 : ℝ) ≤ 2)
  calc
    Real.log 2 =
        2 * (1 / 2 * Real.log ((1 + (1 / 3 : ℝ)) / (1 - 1 / 3))) := by
      norm_num
      ring
    _ ≤ 2 * ((∑ k ∈ range terms,
          (1 / 3 : ℝ) ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) +
            (1 / 3 : ℝ) ^ (2 * terms + 1) / (1 - (1 / 3) ^ 2)) := scaled
    _ = partialSum terms + tailBound terms := by
      rw [mul_add]
      congr 1
      · simp only [partialSum, mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      · simp only [tailBound]
        ring

theorem decimal20 :
    (69314718055994530941 / 10 ^ 20 : ℝ) < Real.log 2 ∧
      Real.log 2 < (69314718055994530942 / 10 ^ 20 : ℝ) := by
  constructor
  · exact lt_of_lt_of_le (by
      norm_num [decimal20Certificate, partialSum, Finset.sum_range_succ])
      (partialSum_le_logTwo decimal20Certificate.terms)
  · exact lt_of_le_of_lt
      (logTwo_le_partialSum_add_tailBound decimal20Certificate.terms) (by
        norm_num [decimal20Certificate, partialSum, tailBound, Finset.sum_range_succ])

theorem decimal50 :
    (69314718055994530941723212145817656807550013436025 / 10 ^ 50 : ℝ) <
        Real.log 2 ∧
      Real.log 2 <
        (69314718055994530941723212145817656807550013436026 / 10 ^ 50 : ℝ) := by
  constructor
  · exact lt_of_lt_of_le (by
      norm_num [decimal50Certificate, partialSum, Finset.sum_range_succ])
      (partialSum_le_logTwo decimal50Certificate.terms)
  · exact lt_of_le_of_lt
      (logTwo_le_partialSum_add_tailBound decimal50Certificate.terms) (by
        norm_num [decimal50Certificate, partialSum, tailBound, Finset.sum_range_succ])

noncomputable def ratio (numerator denominator : Nat) : ℝ :=
  numerator / denominator

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .two, value => value = 2
  | .precision digits, value => value = digits
  | .window window, value =>
      ratio window.lowerNumerator window.lowerDenominator < value ∧
        value < ratio window.upperNumerator window.upperDenominator
  | .empty, _ => False

def sourceModel : Model ℝ :=
  { operation := sourceOperation, relation := fun inputs _ => inputs = [] }

def requestModel : Model ℝ :=
  { operation := requestOperation, relation := fun inputs _ => inputs = [] }

def logModel : Model ℝ :=
  { operation := logOperation
    relation := fun inputs output =>
      match inputs with
      | [input, _precision] => output = Real.log input
      | _ => False }

def operationModels : Array (Model ℝ) :=
  #[sourceModel, requestModel, logModel]

def semantics : Semantics Bound :=
  OperationSemantics.semantics operationModels Contains

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
      if installedEq : installed = previous then
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
      if installedEq : installed = proposed then
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

def stableLaw : StableLaw semantics :=
  OperationSemantics.stableLaw operationModels Contains

def stable : StableStep semantics program program :=
  stableLaw.stable (by rfl) (by rfl) (ProgramPrefix.refl program) (by rfl)

theorem certificateEnclosure (certificate : Certificate)
    (accepted : certificateFor? certificate.digits = some certificate) :
    Contains (.window certificate.window) (Real.log 2) := by
  unfold certificateFor? at accepted
  split at accepted
  · have equal : decimal20Certificate = certificate := Option.some.inj accepted
    rw [← equal]
    have result := decimal20
    norm_num [Contains, Certificate.window, decimal20Certificate, ratio] at result ⊢
    exact result
  · split at accepted
    · have equal : decimal50Certificate = certificate := Option.some.inj accepted
      rw [← equal]
      have result := decimal50
      norm_num [Contains, Certificate.window, decimal50Certificate, ratio] at result ⊢
      exact result
    · contradiction

theorem logEntails (certificate : Certificate)
    (accepted : certificateFor? certificate.digits = some certificate)
    (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (source precision : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 2 })
    (arguments : instruction.args = [source, precision])
    (inputFacts : assumptions =
      [{ node := source, fact := .two },
       { node := precision, fact := .precision certificate.digits }]) :
    semantics.Entails graph assumptions
      { node := output, fact := .window certificate.window } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  have sourceIsTwo : valuation source = 2 := by
    exact holds { node := source, fact := .two } (by simp [inputFacts])
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = Real.log (valuation source) := by
    simpa [logModel, arguments, List.map] using related
  change Contains (.window certificate.window) (valuation output)
  rw [outputEq, sourceIsTwo]
  exact certificateEnclosure certificate accepted

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) :
    fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def exactAction (action : Action) (target : NodeId) : Bool :=
  action.key == logRuleKey && action.node == target

def logFactSchema : PackedFactSchema semantics where
  rule := logRuleKey
  schema := 1
  Certificate := Certificate
  decode := decodeCertificate?
  replay := fun _ action context certificate =>
    if actionExact : exactAction action context.proposed.node then
      if accepted : certificateFor? certificate.digits = some certificate then
        if proposedFact : context.proposed.fact = .window certificate.window then
          match found : context.program.node? context.proposed.node with
          | some instruction =>
              if operation : instruction.op = ({ index := 2 } : OpId) then
                match arguments : instruction.args with
                | [source, precision] =>
                    if inputFacts : context.assumptions =
                        [{ node := source, fact := .two },
                         { node := precision,
                           fact := .precision certificate.digits }] then
                      some
                        { proof := by
                            have proposedEq : context.proposed =
                                { node := context.proposed.node,
                                  fact := .window certificate.window } :=
                              factWith context.proposed proposedFact
                            rw [proposedEq]
                            exact logEntails certificate accepted context.program
                              context.assumptions context.proposed.node instruction
                              source precision found operation arguments inputFacts }
                    else none
                | _ => none
              else none
          | none => none
        else none
      else none
    else none

def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }, emit := { schemas := [] } }

def logProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[logFactSchema] }
    emit := { schemas := [{ key := logFactSchema.key, handle := ``logFactSchema }] } }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, logProof]

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .two },
   { node := node 1, fact := .precision 50 },
   { node := node 2, fact := .all }]

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [program, node]

theorem basePrefix : ProgramPrefix program program :=
  ProgramPrefix.refl program

theorem programPrefix : ProgramPrefix program program :=
  ProgramPrefix.refl program

theorem sameOperations : program.operations = program.operations := rfl

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

theorem targetWithin : (node 2).index < program.nodes.size := by decide

def closeEvidence
    (final : Evidence (semantics.Entails program baseFacts decimal50Input.target)) :
    Evidence (semantics.Entails program baseFacts decimal50Input.target) := final

noncomputable def valuation : NodeId → ℝ
  | ⟨0⟩ => 2
  | ⟨1⟩ => 50
  | ⟨2⟩ => Real.log 2
  | _ => 0

theorem valuationModels : semantics.models program valuation := by
  refine ⟨by simp [program, operations, operationModels, sourceModel,
    requestModel, logModel], ?_⟩
  rintro ⟨index⟩ instruction found
  cases index with
  | zero =>
      simp [Program.node?, program] at found
      subst instruction
      exact ⟨sourceModel, by rfl, by rfl⟩
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, program] at found
          subst instruction
          exact ⟨requestModel, by rfl, by rfl⟩
      | succ index =>
          cases index with
          | zero =>
              simp [Program.node?, program] at found
              subst instruction
              exact ⟨logModel, by rfl, by rfl⟩
          | succ index => simp [Program.node?, program] at found

theorem baseHolds :
    ∀ fact ∈ baseFacts, semantics.holds program valuation fact := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> trivial

end Hex.IntervalMathlib.Experiment.LogTablePrecision

end
