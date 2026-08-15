/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntBKLNWPow
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

namespace Hex.Interval.Experiment.PntBKLNWPow

open Real Finset

/-- Exact PNT+ definition copied from the pinned `BKLNW_a2_bounds.lean`
dependency boundary. -/
noncomputable def sourceF (x : ℝ) : ℝ :=
  ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3)

/-- The same sum after authenticating the upper index for `x = 2^M`. -/
noncomputable def powSum (M : Nat) : ℝ :=
  ∑ k ∈ Icc 3 M, (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / k - 1 / 3))

theorem floorLogTwoPow (M : Nat) :
    ⌊log ((2 : ℝ) ^ M) / log 2⌋₊ = M := by
  rw [log_pow, mul_div_cancel_right₀ _ (ne_of_gt (log_pos one_lt_two))]
  exact Nat.floor_natCast M

theorem sourcePow (M : Nat) : sourceF ((2 : ℝ) ^ M) = powSum M := by
  unfold sourceF powSum
  rw [floorLogTwoPow]
  apply sum_congr rfl
  intro k hk
  rw [Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ 2)]

private theorem termThree (M : Nat) :
    (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / 3 - 1 / 3)) = 1 := by
  norm_num

private theorem termFour {M a : Nat} (ha : 12 * a ≤ M) :
    (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / 4 - 1 / 3)) ≤
      1 / (2 : ℝ) ^ a := by
  rw [show (1 : ℝ) / 4 - 1 / 3 = -(1 / 12) by norm_num]
  have exponent : (M : ℝ) * (-(1 / 12)) ≤ -(a : ℝ) := by
    have haReal : (12 : ℝ) * a ≤ M := by exact_mod_cast ha
    nlinarith
  calc
    (2 : ℝ) ^ ((M : ℝ) * (-(1 / 12))) ≤ (2 : ℝ) ^ (-(a : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) exponent
    _ = 1 / (2 : ℝ) ^ a := by
      rw [Real.rpow_neg_natCast]
      norm_num [zpow_neg]

private theorem termTail {M b k : Nat} (hk : 5 ≤ k) (hb : 15 * b ≤ 2 * M) :
    (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
      1 / (2 : ℝ) ^ b := by
  have kpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 5) hk)
  have reciprocal : (1 : ℝ) / k ≤ 1 / 5 := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hk)
  have exponent :
      (M : ℝ) * ((1 : ℝ) / k - 1 / 3) ≤ -(b : ℝ) := by
    have mnonneg : (0 : ℝ) ≤ M := by positivity
    calc
      (M : ℝ) * ((1 : ℝ) / k - 1 / 3) ≤
          (M : ℝ) * ((1 : ℝ) / 5 - 1 / 3) := by gcongr
      _ ≤ -(b : ℝ) := by
        have hbReal : (15 : ℝ) * b ≤ 2 * M := by exact_mod_cast hb
        norm_num
        nlinarith
  calc
    (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
        (2 : ℝ) ^ (-(b : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) exponent
    _ = 1 / (2 : ℝ) ^ b := by
      rw [Real.rpow_neg_natCast]
      norm_num [zpow_neg]

/-- A parameterized fold bound.  The certificate isolates the `k = 4` term
and bounds every `k ≥ 5` term uniformly; the finite cardinality remains part
of the kernel proof rather than a trusted planner calculation. -/
theorem powSumUpper {M a b : Nat} (hM : 5 ≤ M)
    (ha : 12 * a ≤ M) (hb : 15 * b ≤ 2 * M) :
    powSum M ≤ 1 + 1 / (2 : ℝ) ^ a +
      ((M - 4 : Nat) : ℝ) / (2 : ℝ) ^ b := by
  unfold powSum
  rw [← insert_Icc_add_one_left_eq_Icc (show 3 ≤ M by omega), sum_insert (by simp)]
  simp only [Nat.reduceAdd]
  rw [← insert_Icc_add_one_left_eq_Icc (show 4 ≤ M by omega), sum_insert (by simp)]
  simp only [Nat.cast_ofNat, Nat.reduceAdd]
  rw [termThree, add_assoc]
  gcongr
  · exact termFour ha
  calc
    ∑ k ∈ Icc 5 M, (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
        ∑ _k ∈ Icc 5 M, 1 / (2 : ℝ) ^ b := by
      apply sum_le_sum
      intro k hk
      exact termTail (mem_Icc.mp hk).1 hb
    _ = ((Icc 5 M).card : ℝ) / (2 : ℝ) ^ b := by
      simp [nsmul_eq_mul, div_eq_mul_inv]
    _ = ((M - 4 : Nat) : ℝ) / (2 : ℝ) ^ b := by
      congr 2
      norm_num [Nat.card_Icc]
      omega

private theorem alphaRatio :
    (1 + 193571378 / (10 : ℝ) ^ 16) =
      (alphaNumerator : ℝ) / alphaDenominator := by
  norm_num [alphaNumerator, alphaDenominator]

private theorem sumRatio (value : FoldCertificate) :
    1 + 1 / (2 : ℝ) ^ value.isolatedExponent +
        value.tailCardinality / (2 : ℝ) ^ value.tailExponent =
      (sumNumerator value : ℝ) / sumDenominator value := by
  unfold sumNumerator sumDenominator
  rw [pow_add]
  push_cast
  field_simp

/-- Soundness theorem for every certificate accepted by the pure-natural
checker.  The provider may choose tighter dyadic exponents or a different
rational output cut; replay relies only on `Valid`. -/
theorem certificateUpper (value : FoldCertificate) (valid : Valid value) :
    (1 + 193571378 / (10 : ℝ) ^ 16) *
        sourceF ((2 : ℝ) ^ value.limit) ≤
      (value.targetNumerator : ℝ) / value.targetDenominator := by
  rcases valid with
    ⟨limit, isolated, tailStart, tailCardinality, isolatedExponent,
      tailExponent, targetPositive, targetEnough, targetWithinSource⟩
  have limitAtLeast : 5 ≤ value.limit := by omega
  have count : value.limit - 4 = value.tailCardinality := by omega
  have sumBound :
      powSum value.limit ≤
        1 + 1 / (2 : ℝ) ^ value.isolatedExponent +
          value.tailCardinality / (2 : ℝ) ^ value.tailExponent := by
    simpa [count] using
      powSumUpper limitAtLeast isolatedExponent tailExponent
  rw [sourcePow]
  calc
    (1 + 193571378 / (10 : ℝ) ^ 16) * powSum value.limit ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          (1 + 1 / (2 : ℝ) ^ value.isolatedExponent +
            value.tailCardinality / (2 : ℝ) ^ value.tailExponent) := by
      gcongr
    _ = ((alphaNumerator : ℝ) * sumNumerator value) /
        (alphaDenominator * sumDenominator value) := by
      rw [alphaRatio, sumRatio, div_mul_div_comm]
    _ ≤ (value.targetNumerator : ℝ) / value.targetDenominator := by
      have denominatorPositive :
          (0 : ℝ) < alphaDenominator * sumDenominator value := by
        unfold alphaDenominator sumDenominator
        positivity
      apply (div_le_div_iff₀ denominatorPositive
        (by exact_mod_cast targetPositive)).2
      exact_mod_cast targetEnough

/-- Strong package-owned bound used to replace LeanCert's native-decide-backed
`pow433_upper`. -/
theorem pow433Provider :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (433 : Nat)) ≤
      (100000001948 : ℝ) / 100000000000 := by
  exact certificateUpper certificate (by decide)

/-- Exact theorem shape of PNT+ `cert_pow433_upper`; its final decimal cut is
weaker than the authenticated provider cut. -/
theorem certPow433Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (433 : Nat)) ≤
      (1.00000001937 : ℝ) + (1 : ℝ) / 10 ^ 8 := by
  exact pow433Provider.trans (by norm_num)

theorem oneLeSourcePow {M : Nat} (hM : 3 ≤ M) :
    1 ≤ sourceF ((2 : ℝ) ^ M) := by
  rw [sourcePow]
  unfold powSum
  rw [← insert_Icc_add_one_left_eq_Icc hM, sum_insert (by simp)]
  simp only [Nat.cast_ofNat, Nat.reduceAdd, termThree]
  exact le_add_of_nonneg_right
    (sum_nonneg fun _ _ => Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)

/-- A too-small rational endpoint is mathematically false, not merely
unsupported by the runtime decoder. -/
theorem rejectWrongEndpoint :
    ¬ (1 + 193571378 / (10 : ℝ) ^ 16) *
        sourceF ((2 : ℝ) ^ (433 : Nat)) ≤
      (100000001900 : ℝ) / 100000000000 := by
  have lower :
      (1 + 193571378 / (10 : ℝ) ^ 16) ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          sourceF ((2 : ℝ) ^ (433 : Nat)) := by
    nlinarith [oneLeSourcePow (M := 433) (by norm_num)]
  norm_num at lower ⊢
  linarith

open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

/-- Meaning of the runtime fact lattice. -/
def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .upper, x => x ≤ (1.00000001937 : ℝ) + (1 : ℝ) / 10 ^ 8
  | .empty, _ => False

theorem containsMeet (left right : Bound) (x : ℝ) :
    Contains (Bound.meet left right) x ↔ Contains left x ∧ Contains right x := by
  cases left <;> cases right <;> simp [Bound.meet, Contains]

def foldModel : OperationSemantics.Model ℝ :=
  { operation := foldOperation
    relation := fun inputs output =>
      inputs = [] ∧
        output = (1 + 193571378 / (10 : ℝ) ^ 16) *
          sourceF ((2 : ℝ) ^ (433 : Nat)) }

def operationModels : Array (OperationSemantics.Model ℝ) := #[foldModel]

def semantics : Semantics Bound :=
  OperationSemantics.semantics operationModels Contains

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

theorem checkedUpper (value : FoldCertificate)
    (checked : validCertificate value = true) :
    (1 + 193571378 / (10 : ℝ) ^ 16) *
        sourceF ((2 : ℝ) ^ value.limit) ≤
      (1.00000001937 : ℝ) + (1 : ℝ) / 10 ^ 8 := by
  have valid : Valid value := of_decide_eq_true (by
    simpa [validCertificate] using checked)
  have provider := certificateUpper value valid
  have denominatorPositive : (0 : ℝ) < value.targetDenominator := by
    exact_mod_cast valid.2.2.2.2.2.2.1
  have targetWithin :
      (value.targetNumerator : ℝ) / value.targetDenominator ≤
        (100000002937 : ℝ) / 100000000000 := by
    apply (div_le_div_iff₀ denominatorPositive (by norm_num)).2
    exact_mod_cast valid.2.2.2.2.2.2.2.2
  calc
    _ ≤ (value.targetNumerator : ℝ) / value.targetDenominator := provider
    _ ≤ (100000002937 : ℝ) / 100000000000 := targetWithin
    _ = (1.00000001937 : ℝ) + (1 : ℝ) / 10 ^ 8 := by norm_num

theorem foldEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (nodeValue : Node)
    (found : graph.node? output = some nodeValue)
    (operation : nodeValue.op = ({ index := 0 } : OpId))
    (_arguments : nodeValue.args = []) (_noAssumptions : assumptions = [])
    (value : FoldCertificate) (checked : validCertificate value = true) :
    semantics.Entails graph assumptions { node := output, fact := .upper } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .upper (valuation output)
  intro valuation model _holds
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output nodeValue found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq :
      valuation output = (1 + 193571378 / (10 : ℝ) ^ 16) *
        sourceF ((2 : ℝ) ^ (433 : Nat)) := by
    simpa [foldModel, _arguments, List.map] using related.2
  change valuation output ≤ (1.00000001937 : ℝ) + (1 : ℝ) / 10 ^ 8
  rw [outputEq]
  have valid : Valid value := of_decide_eq_true (by
    simpa [validCertificate] using checked)
  simpa [valid.1] using checkedUpper value checked

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) : fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

/-- Replay checks the graph, the empty assumption list, every certificate
field, and the proposed fact before constructing evidence. -/
def foldFactSchema : PackedFactSchema semantics where
  rule := foldRuleKey
  schema := 1
  Certificate := FoldCertificate
  decode := decodeCertificate?
  replay := fun _ _ context value =>
    if checked : validCertificate value = true then
      if proposedFact : context.proposed.fact = .upper then
        match found : context.program.node? context.proposed.node with
        | some nodeValue =>
            if operation : nodeValue.op = ({ index := 0 } : OpId) then
              if arguments : nodeValue.args = [] then
                if noAssumptions : context.assumptions = [] then
                  some
                    { proof := by
                        have proposedEq :
                            context.proposed =
                              { node := context.proposed.node, fact := .upper } :=
                          factWith context.proposed proposedFact
                        rw [proposedEq]
                        exact foldEntails context.program context.assumptions
                          context.proposed.node nodeValue found operation arguments
                          noAssumptions value checked }
                else none
              else none
            else none
        | none => none
      else none
    else none

def stableLaw : StableLaw semantics :=
  OperationSemantics.stableLaw operationModels Contains

def emitPackage : EmitPackage Lean.Name :=
  { schemas := [{ key := foldFactSchema.key, handle := ``foldFactSchema }] }

def proofPackage : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[foldFactSchema] }
    emit := emitPackage }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[proofPackage]

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

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

noncomputable def valuation : NodeId → ℝ
  | ⟨0⟩ => (1 + 193571378 / (10 : ℝ) ^ 16) *
      sourceF ((2 : ℝ) ^ (433 : Nat))
  | _ => 0

theorem valuationModels : semantics.models program valuation := by
  refine ⟨?_, ?_⟩
  · simp [program, operations, operationModels, foldModel]
  rintro ⟨index⟩ nodeValue found
  cases index with
  | zero =>
      simp [Program.node?, program, instruction] at found
      subst nodeValue
      exact ⟨foldModel, by rfl, by simp [foldModel, valuation]⟩
  | succ index => simp [Program.node?, program] at found

/-- Convert generic replay evidence into the exact PNT+ theorem shape. -/
theorem closePow (result : Evidence
    (semantics.Entails program baseFacts checkerInput.target)) :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (433 : Nat)) ≤
      (1.00000001937 : ℝ) + (1 : ℝ) / 10 ^ 8 := by
  exact result.proof valuation valuationModels (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    trivial)

end Hex.Interval.Experiment.PntBKLNWPow
