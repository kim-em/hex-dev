/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.IntegralCanary
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

namespace Hex.Interval.Experiment.IntegralCanary

open Finset
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

noncomputable def integrand (x : ℝ) : ℝ := Real.exp (-(x ^ 2))

noncomputable def polynomial (x : ℝ) : ℝ :=
  ∑ m ∈ range 8, (-(x ^ 2)) ^ m / m.factorial

noncomputable def approximation : ℝ :=
  ∑ m ∈ range 8, (-1 : ℝ) ^ m / (m.factorial * (2 * m + 1))

private theorem pointwiseError (x : ℝ) (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ‖integrand x - polynomial x‖ ≤ x ^ 16 * (9 / (40320 * 8) : ℝ) := by
  have remainder := Real.exp_bound (x := -(x ^ 2)) (n := 8) (by
    rw [abs_neg, abs_of_nonneg (sq_nonneg x)]
    nlinarith [mul_self_le_mul_self hx.1.le hx.2]) (by norm_num)
  rw [Real.norm_eq_abs]
  norm_num [integrand, polynomial] at remainder ⊢
  convert remainder using 1
  all_goals ring

private theorem polynomialIntegral :
    (∫ x in (0 : ℝ)..1, polynomial x) = approximation := by
  unfold polynomial
  rw [intervalIntegral.integral_finsetSum]
  · unfold approximation
    apply Finset.sum_congr rfl
    intro m _
    calc
      (∫ x in (0 : ℝ)..1, (-(x ^ 2)) ^ m / m.factorial) =
          ∫ x in (0 : ℝ)..1, ((-1 : ℝ) ^ m) * x ^ (2 * m) / m.factorial := by
        apply intervalIntegral.integral_congr
        intro x _
        change (-(x ^ 2)) ^ m / m.factorial =
          ((-1 : ℝ) ^ m) * x ^ (2 * m) / m.factorial
        rw [show -(x ^ 2) = (-1 : ℝ) * x ^ 2 by ring]
        rw [mul_pow, ← pow_mul]
      _ = (-1 : ℝ) ^ m / (m.factorial * (2 * m + 1)) := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
          integral_pow]
        push_cast
        field_simp
        all_goals ring
  · intro m _
    exact Continuous.intervalIntegrable (by fun_prop) 0 1

theorem integralError :
    ‖(∫ x in (0 : ℝ)..1, integrand x) - approximation‖ ≤ 1 / 609280 := by
  rw [← polynomialIntegral]
  rw [← intervalIntegral.integral_sub]
  · calc
      ‖∫ x in (0 : ℝ)..1, integrand x - polynomial x‖ ≤
          ∫ x in (0 : ℝ)..1, x ^ 16 * (9 / (40320 * 8) : ℝ) := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        · filter_upwards with x hx
          exact pointwiseError x hx
        · exact Continuous.intervalIntegrable (by fun_prop) 0 1
      _ = 1 / 609280 := by
        rw [intervalIntegral.integral_mul_const, integral_pow]
        norm_num
  · exact Continuous.intervalIntegrable (by
      unfold integrand
      fun_prop) 0 1
  · exact Continuous.intervalIntegrable (by
      unfold polynomial
      fun_prop) 0 1

theorem approximationValue : approximation = 1009219 / 1351350 := by
  norm_num [approximation, sum_range_succ]

theorem integralWindow :
    (7468 : ℝ) / 10000 < ∫ x in (0 : ℝ)..1, integrand x ∧
      (∫ x in (0 : ℝ)..1, integrand x) < 7469 / 10000 := by
  have error := integralError
  rw [Real.norm_eq_abs, abs_le] at error
  rw [approximationValue] at error
  constructor <;> linarith

/-! # Generic operation semantics and replay -/

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .window7468_7469, x => 7468 / 10000 < x ∧ x < 7469 / 10000
  | .empty, _ => False

def integralModel : OperationSemantics.Model ℝ :=
  { operation := integralOperation
    relation := fun inputs output =>
      inputs = [] ∧ output = ∫ x in (0 : ℝ)..1, integrand x }

def operationModels : Array (OperationSemantics.Model ℝ) := #[integralModel]

def semantics : Semantics Bound :=
  OperationSemantics.semantics operationModels Contains

theorem containsMeet (left right : Bound) (x : ℝ) :
    Contains (left.meet right) x ↔ Contains left x ∧ Contains right x := by
  cases left <;> cases right <;> simp [Bound.meet, Contains]

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
      else none }

def laws : Laws semantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change Contains fact (valuation left) ↔ Contains fact (valuation right)
      rw [values] }

theorem integralEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 0 })
    (arguments : instruction.args = [])
    (_noAssumptions : assumptions = []) :
    semantics.Entails graph assumptions
      { node := output, fact := .window7468_7469 } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .window7468_7469 (valuation output)
  intro valuation model _
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = ∫ x in (0 : ℝ)..1, integrand x := by
    simpa [integralModel, arguments, List.map] using related
  change 7468 / 10000 < valuation output ∧ valuation output < 7469 / 10000
  rw [outputEq]
  exact integralWindow

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) :
    fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

/-- Replay authenticates the full integration recipe before exposing the
four-decimal window. -/
def integralFactSchema : PackedFactSchema semantics where
  rule := integrationRuleKey
  schema := 1
  Certificate := IntegrationCertificate
  decode := decodeCertificate?
  replay := fun _ action context decoded =>
    if certificateShape : decoded = certificate then
      if target : context.proposed.node = action.node then
        if proposedFact : context.proposed.fact = .window7468_7469 then
          match found : context.program.node? action.node with
          | some instruction =>
              if operation : instruction.op = ({ index := 0 } : OpId) then
                if arguments : instruction.args = [] then
                  if noAssumptions : context.assumptions = [] then
                    some
                      { proof := by
                          have proposedEq : context.proposed =
                              { node := action.node, fact := .window7468_7469 } := by
                            rw [factWith context.proposed proposedFact, target]
                          rw [proposedEq]
                          exact integralEntails context.program context.assumptions
                            action.node instruction found operation arguments
                            noAssumptions }
                  else none
                else none
              else none
          | none => none
        else none
      else none
    else none

def stableLaw : StableLaw semantics :=
  OperationSemantics.stableLaw operationModels Contains

def integrationEmit : EmitPackage Lean.Name :=
  { schemas :=
      [{ key := integralFactSchema.key, handle := ``integralFactSchema }] }

def integrationProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[integralFactSchema] }
    emit := integrationEmit }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[integrationProof]

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .all }]

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.all]
    target := { node := node 0, fact := .window7468_7469 } }

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  simp [program, node]

theorem basePrefix : ProgramPrefix program program :=
  ProgramPrefix.refl program

theorem sameOperations : program.operations = program.operations := rfl

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

noncomputable def valuation : NodeId → ℝ
  | ⟨0⟩ => ∫ x in (0 : ℝ)..1, integrand x
  | _ => 0

theorem valuationModels : semantics.models program valuation := by
  refine ⟨?_, ?_⟩
  · simp [program, operations, operationModels, integralModel]
  rintro ⟨index⟩ instruction found
  cases index with
  | zero =>
      simp [Program.node?, program, integralInstruction] at found
      subst instruction
      exact ⟨integralModel, by rfl, by simp [integralModel, valuation]⟩
  | succ index =>
      simp [Program.node?, program] at found

/-- Convert generic replay evidence back to the ordinary definite-integral
statement. -/
theorem closeIntegral
    (result : Evidence
      (semantics.Entails program baseFacts checkerInput.target)) :
    (7468 : ℝ) / 10000 < ∫ x in (0 : ℝ)..1, Real.exp (-(x ^ 2)) ∧
      (∫ x in (0 : ℝ)..1, Real.exp (-(x ^ 2))) < 7469 / 10000 := by
  have holds : ∀ fact, fact ∈ baseFacts →
      Contains fact.fact (valuation fact.node) := by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    trivial
  have closed := result.proof valuation valuationModels holds
  change 7468 / 10000 < valuation (node 0) ∧
    valuation (node 0) < 7469 / 10000 at closed
  simpa [valuation, node, integrand] using closed

end Hex.Interval.Experiment.IntegralCanary
