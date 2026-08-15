/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntExpNegative
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Ordinary-kernel semantics for the PNT+ negative exponential table

A fourteen-term Taylor enclosure proves one package-owned upper cut for
`exp (-1/6)`.  Each authenticated source row then reduces its exact argument
to a natural power of that cut, with an executable integer comparison against
the source endpoint.
-/

namespace Hex.Interval.Experiment.PntExpNegative

open Finset
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

private theorem expWindow (x lower upper : ℝ) (bound : |x| ≤ 1)
    (checkedLower :
      lower < ∑ k ∈ Finset.range 14, x ^ k / Nat.factorial k -
        |x| ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)))
    (checkedUpper :
      ∑ k ∈ Finset.range 14, x ^ k / Nat.factorial k +
        |x| ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) < upper) :
    lower < Real.exp x ∧ Real.exp x < upper := by
  have remainder := Real.exp_bound (x := x) (n := 14) bound (by norm_num)
  rw [abs_le] at remainder
  constructor <;> linarith

/-- The single analytic anchor shared by all 79 source rows. -/
theorem sixthUpper :
    Real.exp (-(1 / 6 : ℝ)) < (846481724891 : ℝ) / 10 ^ 12 := by
  exact (expWindow (-(1 / 6 : ℝ)) 0 ((846481724891 : ℝ) / 10 ^ 12)
    (by norm_num) (by norm_num [Finset.sum_range_succ])
    (by norm_num [Finset.sum_range_succ])).2

private theorem checkedPower (value : Certificate) (valid : value.valid = true) :
    ((value.baseNumerator : ℝ) / 10 ^ value.baseScale) ^ value.sixths <
      (value.numerator : ℝ) / 10 ^ value.scale := by
  simp only [Certificate.valid, Bool.and_eq_true, Certificate.powerCheck,
    decide_eq_true_eq] at valid
  rw [div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast valid.2

/-- Uniform reduction from the checked sixth-root anchor to a source row. -/
theorem certificateUpper (value : Certificate) (valid : value.valid = true) :
    Real.exp (-((value.sixths : ℝ) / 6)) <
      (value.numerator : ℝ) / 10 ^ value.scale := by
  simp only [Certificate.valid, Bool.and_eq_true] at valid
  have shape := valid.1.1
  have baseShape : value.baseNumerator = baseNumerator ∧
      value.baseScale = baseScale := by
    have exactShape : certificateFor? value.sourceIndex = some value := by
      simpa using shape
    simp only [certificateFor?] at exactShape
    split at exactShape
    · simp only [Option.some.injEq] at exactShape
      rw [← exactShape]
      exact ⟨rfl, rfl⟩
    · simp at exactShape
  have base : Real.exp (-(1 / 6 : ℝ)) <
      (value.baseNumerator : ℝ) / 10 ^ value.baseScale := by
    rw [baseShape.1, baseShape.2]
    exact sixthUpper
  have positive : 0 < value.sixths := by
    exact of_decide_eq_true valid.1.2
  have powered := pow_lt_pow_left₀ base (Real.exp_pos _).le positive.ne'
  have reduced : Real.exp (-((value.sixths : ℝ) / 6)) <
      ((value.baseNumerator : ℝ) / 10 ^ value.baseScale) ^ value.sixths := by
    calc
      Real.exp (-((value.sixths : ℝ) / 6)) =
          Real.exp ((value.sixths : ℝ) * (-(1 / 6 : ℝ))) := by
            congr 1
            ring
      _ = Real.exp (-(1 / 6 : ℝ)) ^ value.sixths := by
        rw [Real.exp_nat_mul]
      _ < ((value.baseNumerator : ℝ) / 10 ^ value.baseScale) ^
          value.sixths := powered
  exact reduced.trans (checkedPower value (by
    simp only [Certificate.valid, Bool.and_eq_true]
    exact ⟨⟨shape, valid.1.2⟩, valid.2⟩))

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .exact value, x => x = -((value.sixths : ℝ) / 6)
  | .upper value, x => x < (value.numerator : ℝ) / 10 ^ value.scale
  | .empty, _ => False

def sourceModel : Model ℝ :=
  { operation := sourceOperation, relation := fun inputs _ => inputs = [] }
def expModel : Model ℝ :=
  { operation := expOperation, relation := fun inputs output =>
      match inputs with | [input] => output = Real.exp input | _ => False }
def operationModels : Array (Model ℝ) := #[sourceModel, expModel]
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

theorem expEntails (value : Certificate) (valid : value.valid = true)
    (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (inputFacts : assumptions = [{ node := input, fact := .exact value.source }]) :
    semantics.Entails graph assumptions { node := output, fact := .upper value.upper } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  have inputExact : valuation input = -((value.sixths : ℝ) / 6) := by
    exact holds { node := input, fact := .exact value.source } (by simp [inputFacts])
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = Real.exp (valuation input) := by
    simpa [expModel, arguments, List.map] using related
  change Contains (.upper value.upper) (valuation output)
  rw [outputEq, inputExact]
  simpa [Contains, Certificate.upper] using certificateUpper value valid

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
    if valid : value.valid = true then
      if proposed : context.proposed.fact = .upper value.upper then
        match found : context.program.node? context.proposed.node with
        | some instruction =>
            if operation : instruction.op = ({ index := 1 } : OpId) then
              match arguments : instruction.args with
              | [input] =>
                  if inputFacts : context.assumptions =
                      [{ node := input, fact := .exact value.source }] then
                    some
                      { proof := by
                          have proposedEq : context.proposed =
                              { node := context.proposed.node,
                                fact := .upper value.upper } :=
                            factWith context.proposed proposed
                          rw [proposedEq]
                          exact expEntails value valid context.program context.assumptions
                            context.proposed.node instruction input found operation arguments inputFacts }
                  else none
              | _ => none
            else none
        | none => none
      else none
    else none

def stableLaw : StableLaw semantics := OperationSemantics.stableLaw operationModels Contains
def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }, emit := { schemas := [] } }
def expProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[factSchema] },
    emit := { schemas := [{ key := factSchema.key, handle := ``factSchema }] } }
def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) := #[sourceProof, expProof]

/-! Exact source-shaped wrappers for the complete 79-row subgroup. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1500
theorem exp_neg_10_lt : Real.exp (-(10 : ℝ)) < 4.541e-5 := by
  have result := certificateUpper ((certificateFor? 0).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_21_2_lt : Real.exp (-(21/2 : ℝ)) < 2.755e-5 := by
  have result := certificateUpper ((certificateFor? 1).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_11_lt : Real.exp (-(11 : ℝ)) < 1.672e-5 := by
  have result := certificateUpper ((certificateFor? 2).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_23_2_lt : Real.exp (-(23/2 : ℝ)) < 1.015e-5 := by
  have result := certificateUpper ((certificateFor? 3).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_12_lt : Real.exp (-(12 : ℝ)) < 6.146e-6 := by
  have result := certificateUpper ((certificateFor? 4).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_25_2_lt : Real.exp (-(25/2 : ℝ)) < 3.728e-6 := by
  have result := certificateUpper ((certificateFor? 5).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_13_lt : Real.exp (-(13 : ℝ)) < 2.262e-6 := by
  have result := certificateUpper ((certificateFor? 6).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_40_3_lt : Real.exp (-(40/3 : ℝ)) < 1.621e-6 := by
  have result := certificateUpper ((certificateFor? 7).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_27_2_lt : Real.exp (-(27/2 : ℝ)) < 1.372e-6 := by
  have result := certificateUpper ((certificateFor? 8).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_14_lt : Real.exp (-(14 : ℝ)) < 8.317e-7 := by
  have result := certificateUpper ((certificateFor? 9).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_29_2_lt : Real.exp (-(29/2 : ℝ)) < 5.045e-7 := by
  have result := certificateUpper ((certificateFor? 10).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_44_3_lt : Real.exp (-(44/3 : ℝ)) < 4.271e-7 := by
  have result := certificateUpper ((certificateFor? 11).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_15_lt : Real.exp (-(15 : ℝ)) < 3.061e-7 := by
  have result := certificateUpper ((certificateFor? 12).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_46_3_lt : Real.exp (-(46/3 : ℝ)) < 2.193e-7 := by
  have result := certificateUpper ((certificateFor? 13).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_31_2_lt : Real.exp (-(31/2 : ℝ)) < 1.857e-7 := by
  have result := certificateUpper ((certificateFor? 14).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_16_lt : Real.exp (-(16 : ℝ)) < 1.127e-7 := by
  have result := certificateUpper ((certificateFor? 15).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_33_2_lt : Real.exp (-(33/2 : ℝ)) < 6.827e-8 := by
  have result := certificateUpper ((certificateFor? 16).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_50_3_lt : Real.exp (-(50/3 : ℝ)) < 5.779e-8 := by
  have result := certificateUpper ((certificateFor? 17).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_17_lt : Real.exp (-(17 : ℝ)) < 4.141e-8 := by
  have result := certificateUpper ((certificateFor? 18).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_52_3_lt : Real.exp (-(52/3 : ℝ)) < 2.968e-8 := by
  have result := certificateUpper ((certificateFor? 19).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_35_2_lt : Real.exp (-(35/2 : ℝ)) < 2.512e-8 := by
  have result := certificateUpper ((certificateFor? 20).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_18_lt : Real.exp (-(18 : ℝ)) < 1.524e-8 := by
  have result := certificateUpper ((certificateFor? 21).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_37_2_lt : Real.exp (-(37/2 : ℝ)) < 9.239e-9 := by
  have result := certificateUpper ((certificateFor? 22).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_56_3_lt : Real.exp (-(56/3 : ℝ)) < 7.821e-9 := by
  have result := certificateUpper ((certificateFor? 23).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_19_lt : Real.exp (-(19 : ℝ)) < 5.604e-9 := by
  have result := certificateUpper ((certificateFor? 24).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_58_3_lt : Real.exp (-(58/3 : ℝ)) < 4.016e-9 := by
  have result := certificateUpper ((certificateFor? 25).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_39_2_lt : Real.exp (-(39/2 : ℝ)) < 3.400e-9 := by
  have result := certificateUpper ((certificateFor? 26).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_20_lt : Real.exp (-(20 : ℝ)) < 2.063e-9 := by
  have result := certificateUpper ((certificateFor? 27).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_41_2_lt : Real.exp (-(41/2 : ℝ)) < 1.252e-9 := by
  have result := certificateUpper ((certificateFor? 28).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_62_3_lt : Real.exp (-(62/3 : ℝ)) < 1.060e-9 := by
  have result := certificateUpper ((certificateFor? 29).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_21_lt : Real.exp (-(21 : ℝ)) < 7.584e-10 := by
  have result := certificateUpper ((certificateFor? 30).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_64_3_lt : Real.exp (-(64/3 : ℝ)) < 5.435e-10 := by
  have result := certificateUpper ((certificateFor? 31).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_43_2_lt : Real.exp (-(43/2 : ℝ)) < 4.601e-10 := by
  have result := certificateUpper ((certificateFor? 32).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_22_lt : Real.exp (-(22 : ℝ)) < 2.791e-10 := by
  have result := certificateUpper ((certificateFor? 33).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_45_2_lt : Real.exp (-(45/2 : ℝ)) < 1.693e-10 := by
  have result := certificateUpper ((certificateFor? 34).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_68_3_lt : Real.exp (-(68/3 : ℝ)) < 1.434e-10 := by
  have result := certificateUpper ((certificateFor? 35).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_23_lt : Real.exp (-(23 : ℝ)) < 1.028e-10 := by
  have result := certificateUpper ((certificateFor? 36).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_70_3_lt : Real.exp (-(70/3 : ℝ)) < 7.354e-11 := by
  have result := certificateUpper ((certificateFor? 37).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_47_2_lt : Real.exp (-(47/2 : ℝ)) < 6.226e-11 := by
  have result := certificateUpper ((certificateFor? 38).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_24_lt : Real.exp (-(24 : ℝ)) < 3.777e-11 := by
  have result := certificateUpper ((certificateFor? 39).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_49_2_lt : Real.exp (-(49/2 : ℝ)) < 2.291e-11 := by
  have result := certificateUpper ((certificateFor? 40).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_74_3_lt : Real.exp (-(74/3 : ℝ)) < 1.940e-11 := by
  have result := certificateUpper ((certificateFor? 41).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_25_lt : Real.exp (-(25 : ℝ)) < 1.390e-11 := by
  have result := certificateUpper ((certificateFor? 42).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_76_3_lt : Real.exp (-(76/3 : ℝ)) < 9.953e-12 := by
  have result := certificateUpper ((certificateFor? 43).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_51_2_lt : Real.exp (-(51/2 : ℝ)) < 8.425e-12 := by
  have result := certificateUpper ((certificateFor? 44).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_26_lt : Real.exp (-(26 : ℝ)) < 5.111e-12 := by
  have result := certificateUpper ((certificateFor? 45).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_53_2_lt : Real.exp (-(53/2 : ℝ)) < 3.100e-12 := by
  have result := certificateUpper ((certificateFor? 46).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_80_3_lt : Real.exp (-(80/3 : ℝ)) < 2.625e-12 := by
  have result := certificateUpper ((certificateFor? 47).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_27_lt : Real.exp (-(27 : ℝ)) < 1.881e-12 := by
  have result := certificateUpper ((certificateFor? 48).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_82_3_lt : Real.exp (-(82/3 : ℝ)) < 1.348e-12 := by
  have result := certificateUpper ((certificateFor? 49).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_55_2_lt : Real.exp (-(55/2 : ℝ)) < 1.141e-12 := by
  have result := certificateUpper ((certificateFor? 50).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_28_lt : Real.exp (-(28 : ℝ)) < 6.916e-13 := by
  have result := certificateUpper ((certificateFor? 51).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_57_2_lt : Real.exp (-(57/2 : ℝ)) < 4.195e-13 := by
  have result := certificateUpper ((certificateFor? 52).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_86_3_lt : Real.exp (-(86/3 : ℝ)) < 3.551e-13 := by
  have result := certificateUpper ((certificateFor? 53).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_29_lt : Real.exp (-(29 : ℝ)) < 2.545e-13 := by
  have result := certificateUpper ((certificateFor? 54).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_88_3_lt : Real.exp (-(88/3 : ℝ)) < 1.824e-13 := by
  have result := certificateUpper ((certificateFor? 55).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_59_2_lt : Real.exp (-(59/2 : ℝ)) < 1.544e-13 := by
  have result := certificateUpper ((certificateFor? 56).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_30_lt : Real.exp (-(30 : ℝ)) < 9.359e-14 := by
  have result := certificateUpper ((certificateFor? 57).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_92_3_lt : Real.exp (-(92/3 : ℝ)) < 4.806e-14 := by
  have result := certificateUpper ((certificateFor? 58).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_94_3_lt : Real.exp (-(94/3 : ℝ)) < 2.468e-14 := by
  have result := certificateUpper ((certificateFor? 59).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_32_lt : Real.exp (-(32 : ℝ)) < 1.268e-14 := by
  have result := certificateUpper ((certificateFor? 60).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_98_3_lt : Real.exp (-(98/3 : ℝ)) < 6.503e-15 := by
  have result := certificateUpper ((certificateFor? 61).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_100_3_lt : Real.exp (-(100/3 : ℝ)) < 3.340e-15 := by
  have result := certificateUpper ((certificateFor? 62).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_34_lt : Real.exp (-(34 : ℝ)) < 1.715e-15 := by
  have result := certificateUpper ((certificateFor? 63).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_104_3_lt : Real.exp (-(104/3 : ℝ)) < 8.801e-16 := by
  have result := certificateUpper ((certificateFor? 64).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_106_3_lt : Real.exp (-(106/3 : ℝ)) < 4.519e-16 := by
  have result := certificateUpper ((certificateFor? 65).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_36_lt : Real.exp (-(36 : ℝ)) < 2.321e-16 := by
  have result := certificateUpper ((certificateFor? 66).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_110_3_lt : Real.exp (-(110/3 : ℝ)) < 1.192e-16 := by
  have result := certificateUpper ((certificateFor? 67).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_112_3_lt : Real.exp (-(112/3 : ℝ)) < 6.116e-17 := by
  have result := certificateUpper ((certificateFor? 68).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_38_lt : Real.exp (-(38 : ℝ)) < 3.141e-17 := by
  have result := certificateUpper ((certificateFor? 69).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_116_3_lt : Real.exp (-(116/3 : ℝ)) < 1.613e-17 := by
  have result := certificateUpper ((certificateFor? 70).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_118_3_lt : Real.exp (-(118/3 : ℝ)) < 8.276e-18 := by
  have result := certificateUpper ((certificateFor? 71).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_40_lt : Real.exp (-(40 : ℝ)) < 4.250e-18 := by
  have result := certificateUpper ((certificateFor? 72).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_50_lt : Real.exp (-(50 : ℝ)) < 1e-20 := by
  have result := certificateUpper ((certificateFor? 73).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_200_3_lt : Real.exp (-(200/3 : ℝ)) < 1e-26 := by
  have result := certificateUpper ((certificateFor? 74).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_100_lt : Real.exp (-(100 : ℝ)) < 1e-40 := by
  have result := certificateUpper ((certificateFor? 75).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_400_3_lt : Real.exp (-(400/3 : ℝ)) < 1e-53 := by
  have result := certificateUpper ((certificateFor? 76).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_150_lt : Real.exp (-(150 : ℝ)) < 1e-60 := by
  have result := certificateUpper ((certificateFor? 77).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

theorem exp_neg_200_lt : Real.exp (-(200 : ℝ)) < 1e-80 := by
  have result := certificateUpper ((certificateFor? 78).getD defaultCertificate) (by decide)
  norm_num [certificateFor?, sourceRecord?, defaultCertificate, Certificate.upper,
    Certificate.source] at result ⊢
  exact result

end Hex.Interval.Experiment.PntExpNegative
