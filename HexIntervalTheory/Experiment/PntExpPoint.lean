/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntExpPoint
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Ordinary-kernel semantics for the PNT+ exponential point table

One Taylor/power theorem checks lower and upper exponential cuts. The runtime
record determines the rational step, natural multiplier, Taylor endpoint, and
final source endpoint; no LeanCert theorem is imported.
-/

namespace Hex.Interval.Experiment.PntExpPoint

open Finset
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

noncomputable def signed (negative : Bool) (numerator denominator : Nat) : ℝ :=
  if negative then -((numerator : ℝ) / denominator) else numerator / denominator

noncomputable def Certificate.sourceReal (value : Certificate) : ℝ :=
  signed value.sourceNegative value.sourceNumerator value.sourceDenominator

noncomputable def Certificate.stepReal (value : Certificate) : ℝ :=
  signed value.stepNegative value.stepNumerator value.stepDenominator

noncomputable def Certificate.anchorReal (value : Certificate) : ℝ :=
  value.anchorNumerator / value.anchorDenominator

noncomputable def Certificate.resultReal (value : Certificate) : ℝ :=
  value.resultNumerator / value.resultDenominator

noncomputable def partialSum (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 14, x ^ k / Nat.factorial k

noncomputable def tailBound (x : ℝ) : ℝ :=
  |x| ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14))

theorem taylorLower (x lower : ℝ) (bound : |x| ≤ 1)
    (checked : lower < partialSum x - tailBound x) : lower < Real.exp x := by
  have remainder := Real.exp_bound (x := x) (n := 14) bound (by norm_num)
  rw [abs_le] at remainder
  dsimp [partialSum, tailBound] at checked
  linarith

theorem taylorUpper (x upper : ℝ) (bound : |x| ≤ 1)
    (checked : partialSum x + tailBound x < upper) : Real.exp x < upper := by
  have remainder := Real.exp_bound (x := x) (n := 14) bound (by norm_num)
  rw [abs_le] at remainder
  dsimp [partialSum, tailBound] at checked
  linarith

theorem poweredLower (source step anchor result : ℝ) (power : Nat)
    (positivePower : 0 < power) (sourceShape : source = power * step)
    (stepBound : |step| ≤ 1)
    (anchorCheck : anchor < partialSum step - tailBound step)
    (anchorNonnegative : 0 ≤ anchor) (resultCheck : result ≤ anchor ^ power) :
    result < Real.exp source := by
  have point := taylorLower step anchor stepBound anchorCheck
  have powered := pow_lt_pow_left₀ point anchorNonnegative positivePower.ne'
  rw [← Real.exp_nat_mul, ← sourceShape] at powered
  exact resultCheck.trans_lt powered

theorem poweredUpper (source step anchor result : ℝ) (power : Nat)
    (positivePower : 0 < power) (sourceShape : source = power * step)
    (stepBound : |step| ≤ 1)
    (anchorCheck : partialSum step + tailBound step < anchor)
    (resultCheck : anchor ^ power ≤ result) : Real.exp source < result := by
  have point := taylorUpper step anchor stepBound anchorCheck
  have powered := pow_lt_pow_left₀ point (Real.exp_pos step).le positivePower.ne'
  rw [← Real.exp_nat_mul, ← sourceShape] at powered
  exact powered.trans_le resultCheck

private theorem negOneBound :
    (367879441 / 1000000000 : ℝ) < Real.exp (-1) := by
  apply poweredLower (-1) (-1) (367879441 / 1000000000)
    (367879441 / 1000000000) 1 <;>
    norm_num [partialSum, tailBound, Finset.sum_range_succ]

private theorem negHalfBound :
    Real.exp (-(1 / 2 : ℝ)) < 6065307 / 10000000 := by
  apply poweredUpper (-(1 / 2)) (-(1 / 2)) (6065307 / 10000000)
    (6065307 / 10000000) 1 <;>
    norm_num [partialSum, tailBound, Finset.sum_range_succ]

private theorem negTwoThirdsBound :
    Real.exp (-(2 / 3 : ℝ)) < 513418 / 1000000 := by
  apply poweredUpper (-(2 / 3)) (-(2 / 3)) (513418 / 1000000)
    (513418 / 1000000) 1 <;>
    norm_num [partialSum, tailBound, Finset.sum_range_succ]

private theorem negFiftyBound :
    Real.exp (-(50 : ℝ)) < 1 / 100000000000000000000 := by
  apply poweredUpper (-50) (-1) (46 / 125) (1 / 100000000000000000000) 50 <;>
    norm_num [partialSum, tailBound, Finset.sum_range_succ]

private theorem one112Bound : Real.exp (139 / 125 : ℝ) < 3041 / 1000 := by
  apply poweredUpper (139 / 125) (139 / 250) (8719 / 5000) (3041 / 1000) 2 <;>
    norm_num [partialSum, tailBound, Finset.sum_range_succ]

private theorem twoBound : Real.exp 2 < 8 := by
  apply poweredUpper 2 (1 / 2) (1649 / 1000) 8 4 <;>
    norm_num [partialSum, tailBound, Finset.sum_range_succ]

private theorem twentyBound : Real.exp 20 < 485165196 := by
  apply poweredUpper 20 (1 / 2) (164872127071 / 100000000000)
    485165196 40 <;>
    norm_num [partialSum, tailBound, Finset.sum_range_succ]

private theorem twentyTwoBound : (1000000000 : ℝ) < Real.exp 22 := by
  apply poweredLower 22 1 (27 / 10) 1000000000 22 <;>
    norm_num [partialSum, tailBound, Finset.sum_range_succ]

private theorem negThirteenHalfBound :
    (1 / 900000 : ℝ) < Real.exp (-(27 / 2)) := by
  apply poweredLower (-(27 / 2)) (-(1 / 2)) (1213 / 2000) (1 / 900000) 27 <;>
    norm_num [partialSum, tailBound, Finset.sum_range_succ]

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .exact value, x =>
      x = signed value.negative value.numerator value.denominator
  | .lower value, x => (value.numerator : ℝ) / value.denominator < x
  | .upper value, x => x < (value.numerator : ℝ) / value.denominator
  | .empty, _ => False

theorem certificateContains (value : Certificate)
    (accepted : rowFor? value.sourceIndex = some value) :
    Contains value.result (Real.exp value.sourceReal) := by
  have member : value ∈ rows := List.mem_of_find?_eq_some accepted
  simp [rows] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [Certificate.result, Certificate.cut, Certificate.sourceReal, rowNegOne,
      row, Contains, signed] using negOneBound
  · simpa [Certificate.result, Certificate.cut, Certificate.sourceReal, rowNegHalf,
      row, Contains, signed] using negHalfBound
  · simpa [Certificate.result, Certificate.cut, Certificate.sourceReal,
      rowNegTwoThirds, row, Contains, signed] using negTwoThirdsBound
  · simpa [Certificate.result, Certificate.cut, Certificate.sourceReal,
      rowNegFifty, row, Contains, signed] using negFiftyBound
  · simpa [Certificate.result, Certificate.cut, Certificate.sourceReal, rowOne112,
      row, Contains, signed] using one112Bound
  · simpa [Certificate.result, Certificate.cut, Certificate.sourceReal, rowTwo,
      row, Contains, signed] using twoBound
  · simpa [Certificate.result, Certificate.cut, Certificate.sourceReal, rowTwenty,
      row, Contains, signed] using twentyBound
  · simpa [Certificate.result, Certificate.cut, Certificate.sourceReal,
      rowTwentyTwo, row, Contains, signed] using twentyTwoBound
  · simpa [Certificate.result, Certificate.cut, Certificate.sourceReal,
      rowNegThirteenHalf, row, Contains, signed] using negThirteenHalfBound

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

theorem expEntails (value : Certificate)
    (accepted : rowFor? value.sourceIndex = some value)
    (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (inputFacts : assumptions = [{ node := input, fact := .exact value.source }]) :
    semantics.Entails graph assumptions { node := output, fact := value.result } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  have inputExact : valuation input = value.sourceReal := by
    exact holds { node := input, fact := .exact value.source } (by simp [inputFacts])
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = Real.exp (valuation input) := by
    simpa [expModel, arguments, List.map] using related
  change Contains value.result (valuation output)
  rw [outputEq, inputExact]
  exact certificateContains value accepted

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
    if accepted : rowFor? value.sourceIndex = some value then
      if proposed : context.proposed.fact = value.result then
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
                              { node := context.proposed.node, fact := value.result } :=
                            factWith context.proposed proposed
                          rw [proposedEq]
                          exact expEntails value accepted context.program context.assumptions
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
def expProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[factSchema] },
    emit := { schemas := [{ key := factSchema.key, handle := ``factSchema }] } }
def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) := #[sourceProof, expProof]

/-! Exact source-shaped wrappers for all nine exponential sites. -/

theorem exp_neg_one_gt : (0.367879441 : ℝ) < Real.exp (-1 : ℝ) := by
  have bound := negOneBound
  norm_num at bound ⊢
  exact bound

theorem exp_neg_half_lt : Real.exp (-(1 / 2 : ℝ)) < 0.6065307 := by
  have bound := negHalfBound
  norm_num at bound ⊢
  exact bound

theorem exp_neg_two_thirds_lt : Real.exp (-(2 / 3 : ℝ)) < 0.513418 := by
  have bound := negTwoThirdsBound
  norm_num at bound ⊢
  exact bound

theorem exp_neg_lt_1e_neg_20 {x : ℝ} (hx : 50 ≤ x) :
    Real.exp (-x) < 1e-20 := by
  have boundary : Real.exp (-(50 : ℝ)) < (1 / 10 ^ 20 : ℝ) := by
    have bound := negFiftyBound
    norm_num at bound ⊢
    exact bound
  have monotone := Real.exp_le_exp.mpr (show -x ≤ -(50 : ℝ) by linarith)
  norm_num [OfScientific.ofScientific] at boundary ⊢
  exact monotone.trans_lt boundary

theorem exp_1_112_lt : Real.exp (1.112 : ℝ) < 3.041 := by
  have bound := one112Bound
  norm_num at bound ⊢
  exact bound

theorem exp_two_lt_eight : Real.exp 2 < 8 := twoBound

theorem exp_20_le : Real.exp 20 ≤ 485165196 := twentyBound.le

theorem one_e9_le_exp_22 : (1e9 : ℝ) ≤ Real.exp 22 := by
  have bound := twentyTwoBound
  norm_num [OfScientific.ofScientific] at bound ⊢
  exact bound.le

theorem inv_900000_le_exp_neg_13_5 :
    (1 / 900000 : ℝ) ≤ Real.exp (-(13.5 : ℝ)) := by
  have bound := negThirteenHalfBound
  norm_num at bound ⊢
  exact bound.le

/-! Generic proof-frontend fixture at the tight high-power `exp 20` row. -/

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .exact rowTwenty.source },
   { node := node 1, fact := .all }]

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [program, node]

theorem basePrefix : ProgramPrefix program program := ProgramPrefix.refl program
theorem sameOperations : program.operations = program.operations := rfl

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

noncomputable def valuation : NodeId → ℝ
  | ⟨0⟩ => 20
  | ⟨1⟩ => Real.exp 20
  | _ => 0

theorem valuationModels : semantics.models program valuation := by
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
      | succ index => simp [Program.node?, program] at found

theorem closeExpTwenty
    (result : Evidence
      (semantics.Entails program baseFacts representativeInput.target)) :
    Real.exp 20 < 485165196 := by
  have closed := result.proof valuation valuationModels (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change Contains (.exact rowTwenty.source) (valuation (node 0))
      norm_num [Contains, Certificate.source, rowTwenty, row, signed, valuation, node]
    · trivial)
  change Contains rowTwenty.result (valuation (node 1)) at closed
  norm_num [Contains, Certificate.result, Certificate.cut, rowTwenty, row,
    valuation, node] at closed ⊢
  exact closed

end Hex.Interval.Experiment.PntExpPoint
