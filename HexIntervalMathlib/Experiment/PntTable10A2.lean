/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntBKLNWExp
public import HexInterval.Experiment.PntTable10A2

@[expose] public section

/-!
# Ordinary-kernel semantics for the BKLNW Table 10 `a₂` batch

This companion copies the exact mathematical shape of PNT+'s `Inputs.a₂`
after unfolding its fixed default alpha.  One head-plus-tail proof covers all
38 source rows and is independent of every Table 10 target-coordinate bound.
-/

namespace Hex.Interval.Experiment.PntTable10A2

open Real Finset
open PntBKLNWExp

/-- Pinned PNT+ `Inputs.default.a₂` after unfolding the default alpha and
replacing PNT+'s `f` by its exact copied definition `sourceF`. -/
noncomputable def sourceA2 (b : ℝ) : ℝ :=
  (1 + 193571378 / (10 : ℝ) ^ 16) *
    max (PntBKLNWPow.sourceF (Real.exp b))
      (PntBKLNWPow.sourceF
        ((2 : ℝ) ^ (⌊b / Real.log 2⌋₊ + 1)))

private theorem floorFromWindow (b N : Nat)
    (lowerCheck : N * logUpperNumerator ≤ b * logDenominator)
    (upperCheck : b * logDenominator < (N + 1) * logLowerNumerator) :
    ⌊(b : ℝ) / Real.log 2⌋₊ = N := by
  rw [Nat.floor_eq_iff (div_nonneg (by positivity)
    (Real.log_nonneg (by norm_num)))]
  have logWindow :=
    Hex.IntervalMathlib.Experiment.LogTablePrecision.decimal20
  constructor
  · apply (le_div_iff₀ (Real.log_pos (by norm_num))).2
    have checked : (N : ℝ) * 69314718055994530942 ≤
        b * 10 ^ 20 := by
      exact_mod_cast lowerCheck
    norm_num [logUpperNumerator, logDenominator] at checked ⊢
    nlinarith [logWindow.2]
  · apply (div_lt_iff₀ (Real.log_pos (by norm_num))).2
    have checked : (b : ℝ) * 10 ^ 20 <
        (N + 1 : Nat) * 69314718055994530941 := by
      exact_mod_cast upperCheck
    norm_num [logLowerNumerator, logDenominator] at checked ⊢
    nlinarith [logWindow.1]

theorem sourceFloor (value : Certificate) (valid : Valid value) :
    ⌊(value.argument : ℝ) / Real.log 2⌋₊ = value.floor := by
  rcases valid with
    ⟨_index, _source, lower, upper, scale, _base, _floorAtLeast,
      lowerCheck, upperCheck, _targetPositive, _target⟩
  rw [upper, scale] at lowerCheck
  rw [lower, scale] at upperCheck
  exact floorFromWindow value.argument value.floor lowerCheck upperCheck

private theorem sourceExp (value : Certificate) (valid : Valid value) :
    PntBKLNWPow.sourceF (Real.exp value.argument) =
      PntBKLNWExp.expSum value.argument value.floor := by
  unfold PntBKLNWPow.sourceF PntBKLNWExp.expSum
  rw [Real.log_exp, sourceFloor value valid]
  apply sum_congr rfl
  intro k _member
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]

private theorem sourcePowLe (value : Certificate) (valid : Valid value) :
    PntBKLNWPow.sourceF ((2 : ℝ) ^ (value.floor + 1)) ≤
      PntBKLNWExp.expSum value.argument (value.floor + 1) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hidx :
      ⌊Real.log ((2 : ℝ) ^ (value.floor + 1)) / Real.log 2⌋₊ =
        value.floor + 1 := by
    rw [Real.log_pow, mul_div_assoc, div_self hlog2.ne', mul_one,
      Nat.floor_natCast]
  have hexpLe : Real.exp value.argument ≤
      (2 : ℝ) ^ (value.floor + 1) := by
    have floorEq := sourceFloor value valid
    have floorLt : (value.argument : ℝ) / Real.log 2 <
        (value.floor : ℝ) + 1 := by
      have := Nat.lt_floor_add_one
        ((value.argument : ℝ) / Real.log 2)
      rw [floorEq] at this
      exact_mod_cast this
    have argumentLt : (value.argument : ℝ) <
        ((value.floor : ℝ) + 1) * Real.log 2 := by
      calc
        (value.argument : ℝ) =
            ((value.argument : ℝ) / Real.log 2) * Real.log 2 := by
              field_simp
        _ < ((value.floor : ℝ) + 1) * Real.log 2 :=
          mul_lt_mul_of_pos_right floorLt hlog2
    calc
      Real.exp value.argument ≤
          Real.exp (((value.floor : ℝ) + 1) * Real.log 2) :=
        Real.exp_le_exp.mpr argumentLt.le
      _ = (2 : ℝ) ^ (value.floor + 1) := by
        rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
          show ((value.floor : ℝ) + 1) =
            ((value.floor + 1 : Nat) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
  unfold PntBKLNWPow.sourceF PntBKLNWExp.expSum
  rw [hidx]
  apply sum_le_sum
  intro k member
  have hk3 : 3 ≤ k := (mem_Icc.mp member).1
  have exponentNonpositive :
      (1 : ℝ) / (k : ℝ) - 1 / 3 ≤ 0 := by
    have hkr : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
    have reciprocal : (1 : ℝ) / (k : ℝ) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) hkr
    linarith
  rw [Real.rpow_def_of_pos (by positivity :
    (0 : ℝ) < (2 : ℝ) ^ (value.floor + 1))]
  apply Real.exp_le_exp.mpr
  have logLe : (value.argument : ℝ) ≤
      Real.log ((2 : ℝ) ^ (value.floor + 1)) := by
    calc
      (value.argument : ℝ) = Real.log (Real.exp value.argument) :=
        (Real.log_exp _).symm
      _ ≤ Real.log ((2 : ℝ) ^ (value.floor + 1)) :=
        Real.log_le_log (Real.exp_pos _) hexpLe
  nlinarith [logLe, exponentNonpositive]

private theorem termUpper {b k : Nat} (lower : 4 ≤ k) (upper : k ≤ 13) :
    Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
      PntBKLNWExp.upperBaseValue k ^ b := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by positivity)
    (PntBKLNWExp.baseWindow lower (upper.trans (by decide))).2.le b

private theorem tailUpper {b k : Nat} (lower : 13 ≤ k) :
    Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
      PntBKLNWExp.upperBaseValue 13 ^ b := by
  rw [Real.exp_nat_mul]
  apply pow_le_pow_left₀ (by positivity)
  calc
    Real.exp ((1 : ℝ) / k - 1 / 3) ≤
        Real.exp ((1 : ℝ) / 13 - 1 / 3) := by
      apply Real.exp_le_exp.mpr
      have reciprocal : (1 : ℝ) / k ≤ 1 / 13 :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast lower)
      linarith
    _ ≤ PntBKLNWExp.upperBaseValue 13 :=
      (PntBKLNWExp.baseWindow (by decide) (by decide)).2.le

noncomputable def upperHead (b : Nat) : ℝ :=
  ∑ k ∈ Icc 4 12, PntBKLNWExp.upperBaseValue k ^ b

noncomputable def upperValue (value : Certificate) : ℝ :=
  1 + upperHead value.argument +
    (tailCardinality value : ℝ) *
      PntBKLNWExp.upperBaseValue 13 ^ value.argument

private theorem expSumUpper (value : Certificate) (valid : Valid value) :
    PntBKLNWExp.expSum value.argument (value.floor + 1) ≤
      upperValue value := by
  have floorAtLeast : 12 ≤ value.floor := valid.2.2.2.2.2.2.1
  unfold PntBKLNWExp.expSum upperValue upperHead
  rw [← insert_Icc_add_one_left_eq_Icc (show 3 ≤ value.floor + 1 by omega),
    sum_insert (by simp)]
  have term3 :
      Real.exp ((value.argument : ℝ) * ((1 : ℝ) / (3 : Nat) - 1 / 3)) =
        1 := by norm_num
  rw [term3]
  simp only [Nat.reduceAdd]
  have union : Icc (4 : Nat) (value.floor + 1) =
      Icc 4 12 ∪ Icc 13 (value.floor + 1) := by
    ext k
    simp only [mem_Icc, mem_union]
    omega
  have disjoint : Disjoint (Icc (4 : Nat) 12)
      (Icc 13 (value.floor + 1)) := by
    simp only [Finset.disjoint_left, mem_Icc]
    omega
  rw [union, sum_union disjoint]
  have headBound :
      (∑ k ∈ Icc (4 : Nat) 12,
          Real.exp ((value.argument : ℝ) * ((1 : ℝ) / k - 1 / 3))) ≤
        ∑ k ∈ Icc (4 : Nat) 12,
          PntBKLNWExp.upperBaseValue k ^ value.argument := by
    apply sum_le_sum
    intro k member
    exact termUpper (mem_Icc.mp member).1
      ((mem_Icc.mp member).2.trans (by decide))
  have tailBound :
      (∑ k ∈ Icc (13 : Nat) (value.floor + 1),
          Real.exp ((value.argument : ℝ) * ((1 : ℝ) / k - 1 / 3))) ≤
        (tailCardinality value : ℝ) *
          PntBKLNWExp.upperBaseValue 13 ^ value.argument := by
    calc
      ∑ k ∈ Icc (13 : Nat) (value.floor + 1),
          Real.exp ((value.argument : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
          ∑ _k ∈ Icc (13 : Nat) (value.floor + 1),
            PntBKLNWExp.upperBaseValue 13 ^ value.argument := by
        apply sum_le_sum
        intro k member
        exact tailUpper (mem_Icc.mp member).1
      _ = ((Icc (13 : Nat) (value.floor + 1)).card : ℝ) *
          PntBKLNWExp.upperBaseValue 13 ^ value.argument := by simp
      _ = (tailCardinality value : ℝ) *
          PntBKLNWExp.upperBaseValue 13 ^ value.argument := by
        congr 2
        norm_num [Nat.card_Icc, tailCardinality]
        omega
  linarith

private theorem sourceExpLeSucc (value : Certificate) (valid : Valid value) :
    PntBKLNWPow.sourceF (Real.exp value.argument) ≤
      PntBKLNWExp.expSum value.argument (value.floor + 1) := by
  rw [sourceExp value valid]
  unfold PntBKLNWExp.expSum
  rw [sum_Icc_succ_top (show 3 ≤ value.floor + 1 by
    have := valid.2.2.2.2.2.2.1
    omega)]
  exact le_add_of_nonneg_right (Real.exp_nonneg _)

private theorem bandRatio (b stop : Nat) :
    (∑ k ∈ Icc 4 stop,
        ((PntBKLNWExp.upperBaseNumerator k : ℝ) /
          PntBKLNWExp.baseDenominator) ^ b) =
      (PntBKLNWExp.bandPowerSum PntBKLNWExp.upperBaseNumerator b stop : ℝ) /
        PntBKLNWExp.baseDenominator ^ b := by
  induction stop with
  | zero => simp [PntBKLNWExp.bandPowerSum]
  | succ stop ih =>
      by_cases h : 4 ≤ stop + 1
      · rw [sum_Icc_succ_top h, PntBKLNWExp.bandPowerSum, ite_eq_left h, ih]
        rw [div_pow]
        push_cast
        field_simp
      · have empty : Icc 4 (stop + 1) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro k member
          have bounds := mem_Icc.mp member
          omega
        rw [empty]
        simp [PntBKLNWExp.bandPowerSum, h]

private theorem alphaRatio :
    (1 + 193571378 / (10 : ℝ) ^ 16) =
      (PntBKLNWExp.alphaNumerator : ℝ) /
        PntBKLNWExp.alphaDenominator := by
  norm_num [PntBKLNWExp.alphaNumerator, PntBKLNWExp.alphaDenominator]

private theorem upperRatio (value : Certificate)
    (base : value.baseScale = PntBKLNWExp.baseDenominator) :
    upperValue value =
      (upperSumNumerator value : ℝ) / sumDenominator value := by
  unfold upperValue upperHead upperSumNumerator sumDenominator
    PntBKLNWExp.upperBaseValue
  rw [base, bandRatio]
  rw [div_pow]
  push_cast
  field_simp [PntBKLNWExp.baseDenominator]

/-- One reusable ordinary-kernel theorem for every runtime-accepted source
row.  Its proof consumes the authenticated log window, finite table, floor,
tail count, target endpoint, and rational scale. -/
theorem certificateUpper (value : Certificate) (valid : Valid value) :
    sourceA2 value.argument ≤
      (value.targetNumerator : ℝ) / value.targetDenominator := by
  rcases valid with
    ⟨index, source, lower, upper, scale, base, floorAtLeast,
      lowerCheck, upperCheck, targetPositive, target⟩
  have valid' : Valid value :=
    ⟨index, source, lower, upper, scale, base, floorAtLeast,
      lowerCheck, upperCheck, targetPositive, target⟩
  have expBound := (sourceExpLeSucc value valid').trans
    (expSumUpper value valid')
  have powBound := (sourcePowLe value valid').trans
    (expSumUpper value valid')
  unfold sourceA2
  rw [sourceFloor value valid']
  calc
    (1 + 193571378 / (10 : ℝ) ^ 16) *
        max (PntBKLNWPow.sourceF (Real.exp value.argument))
          (PntBKLNWPow.sourceF
            ((2 : ℝ) ^ (value.floor + 1))) ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) * upperValue value := by
      gcongr
      exact max_le expBound powBound
    _ = ((PntBKLNWExp.alphaNumerator : ℝ) * upperSumNumerator value) /
        (PntBKLNWExp.alphaDenominator * sumDenominator value) := by
      rw [alphaRatio, upperRatio value base, div_mul_div_comm]
    _ ≤ (value.targetNumerator : ℝ) / value.targetDenominator := by
      have denominatorPositive :
          (0 : ℝ) < PntBKLNWExp.alphaDenominator * sumDenominator value := by
        unfold PntBKLNWExp.alphaDenominator sumDenominator
        rw [base]
        unfold PntBKLNWExp.baseDenominator
        positivity
      apply (div_le_div_iff₀ denominatorPositive
        (by exact_mod_cast targetPositive)).2
      exact_mod_cast target

/-- Source-dispatch-shaped replacement for the 38 pinned `rowNN_a2_le`
declarations.  PNT+ can unfold `Inputs.default.a₂` and locally change its
goal to this exact copied `sourceA2` shape. -/
theorem rowOfMem (value : Certificate) (member : value ∈ certificates) :
    sourceA2 value.argument ≤
      (value.targetNumerator : ℝ) / value.targetDenominator := by
  have allValid : certificates.all validCertificate = true := by
    set_option exponentiation.threshold 500 in decide
  have checked := (List.all_eq_true.mp allValid) value member
  exact certificateUpper value
    (of_decide_eq_true (by simpa [validCertificate] using checked))

open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

def Contains (expected : Certificate) : Bound → ℝ → Prop
  | .all, _ => True
  | .upper, x =>
      x ≤ (expected.targetNumerator : ℝ) / expected.targetDenominator
  | .empty, _ => False

theorem containsMeet (expected : Certificate) (left right : Bound) (x : ℝ) :
    Contains expected (Bound.meet left right) x ↔
      Contains expected left x ∧ Contains expected right x := by
  cases left <;> cases right <;> simp [Bound.meet, Contains]

def foldModel (expected : Certificate) : OperationSemantics.Model ℝ :=
  { operation := foldOperation
    relation := fun inputs output =>
      inputs = [] ∧ output = sourceA2 expected.argument }

def operationModels (expected : Certificate) :
    Array (OperationSemantics.Model ℝ) := #[foldModel expected]

def semantics (expected : Certificate) : Semantics Bound :=
  OperationSemantics.semantics (operationModels expected) (Contains expected)

def boundSchema (expected : Certificate) : FactDomainSchema (semantics expected) :=
  { top := fun _ => .all
    topSound := by intros; trivial
    proveMeet := fun _ _ previous proposed installed =>
      if exact : installed = previous.meet proposed then
        some
          { proof := by
              subst installed
              intro valuation _
              exact containsMeet expected previous proposed (valuation _) }
      else none }

def laws (expected : Certificate) : Laws (semantics expected) :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change Contains expected fact (valuation left) ↔
        Contains expected fact (valuation right)
      rw [values] }

theorem checkedUpper (value : Certificate)
    (checked : validCertificate value = true) :
    sourceA2 value.argument ≤
      (value.targetNumerator : ℝ) / value.targetDenominator := by
  apply certificateUpper value
  exact of_decide_eq_true (by simpa [validCertificate] using checked)

theorem foldEntails (expected : Certificate)
    (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (nodeValue : Node)
    (found : graph.node? output = some nodeValue)
    (operation : nodeValue.op = ({ index := 0 } : OpId))
    (_arguments : nodeValue.args = []) (_noAssumptions : assumptions = [])
    (value : Certificate) (same : value = expected)
    (checked : validCertificate value = true) :
    (semantics expected).Entails graph assumptions
      { node := output, fact := .upper } := by
  subst value
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models (operationModels expected) graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains expected assumption.fact (valuation assumption.node)) →
      Contains expected .upper (valuation output)
  intro valuation model _holds
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output nodeValue found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = sourceA2 expected.argument := by
    simpa [foldModel, _arguments, List.map] using related.2
  change valuation output ≤
    (expected.targetNumerator : ℝ) / expected.targetDenominator
  rw [outputEq]
  exact checkedUpper expected checked

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) : fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def foldFactSchema (expected : Certificate) :
    PackedFactSchema (semantics expected) where
  rule := foldRuleKey
  schema := 1
  Certificate := Certificate
  decode := decodeCertificate?
  replay := fun _ _ context value =>
    if checked : validCertificate value = true then
      if same : value = expected then
        if proposedFact : context.proposed.fact = .upper then
          match found : context.program.node? context.proposed.node with
          | some nodeValue =>
              if operation : nodeValue.op = ({ index := 0 } : OpId) then
                if arguments : nodeValue.args = [] then
                  if noAssumptions : context.assumptions = [] then
                    some
                      { proof := by
                          have proposedEq : context.proposed =
                              { node := context.proposed.node, fact := .upper } :=
                            factWith context.proposed proposedFact
                          rw [proposedEq]
                          exact foldEntails expected context.program
                            context.assumptions context.proposed.node nodeValue found
                            operation arguments noAssumptions value same checked }
                  else none
                else none
              else none
          | none => none
        else none
      else none
    else none

def stableLaw (expected : Certificate) : StableLaw (semantics expected) :=
  OperationSemantics.stableLaw (operationModels expected) (Contains expected)

def emitPackage (expected : Certificate) : EmitPackage Lean.Name :=
  let schema := foldFactSchema expected
  { schemas := [{ key := schema.key, handle := ``foldFactSchema }] }

def proofPackage (expected : Certificate) :
    ProofRegistry.Package (semantics expected) Lean.Name :=
  { semantic := { factSchemas := #[foldFactSchema expected] }
    emit := emitPackage expected }

def proofPackages (expected : Certificate) :
    Array (ProofRegistry.Package (semantics expected) Lean.Name) :=
  #[proofPackage expected]

def row21FactSchema : PackedFactSchema (semantics row21) :=
  foldFactSchema row21

def row21EmitPackage : EmitPackage Lean.Name :=
  { schemas := [{ key := row21FactSchema.key, handle := ``row21FactSchema }] }

def row21ProofPackage : ProofRegistry.Package (semantics row21) Lean.Name :=
  { semantic := { factSchemas := #[row21FactSchema] }
    emit := row21EmitPackage }

def row21ProofPackages :
    Array (ProofRegistry.Package (semantics row21) Lean.Name) :=
  #[row21ProofPackage]

def baseFacts : List (NodeFact Bound) := [{ node, fact := .all }]

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.all]
    target := { node, fact := .upper } }

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  simp [program, node]

theorem basePrefix : ProgramPrefix program program := ProgramPrefix.refl program
theorem sameOperations : program.operations = program.operations := rfl

def initialExtension (expected : Certificate) :
    Evidence ((semantics expected).Extends program program) :=
  extendRefl (semantics expected) program

noncomputable def valuation (expected : Certificate) : NodeId → ℝ
  | ⟨0⟩ => sourceA2 expected.argument
  | _ => 0

theorem valuationModels (expected : Certificate) :
    (semantics expected).models program (valuation expected) := by
  refine ⟨?_, ?_⟩
  · simp [program, operations, operationModels, foldModel]
  rintro ⟨index⟩ nodeValue found
  cases index with
  | zero =>
      simp [Program.node?, program, instruction] at found
      subst nodeValue
      exact ⟨foldModel expected, by rfl, by simp [foldModel, valuation]⟩
  | succ index => simp [Program.node?, program] at found

theorem closeUpper (expected : Certificate) (result : Evidence
    ((semantics expected).Entails program baseFacts checkerInput.target)) :
    sourceA2 expected.argument ≤
      (expected.targetNumerator : ℝ) / expected.targetDenominator := by
  exact result.proof (valuation expected) (valuationModels expected) (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    trivial)

end Hex.Interval.Experiment.PntTable10A2
