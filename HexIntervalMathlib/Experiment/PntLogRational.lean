/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntLogRational
public import HexIntervalMathlib.Experiment.PntLogNatural
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Ordinary-kernel semantics for the PNT+ rational logarithm table

The provider extends the accepted natural-log atanh identity to positive
rational inputs. Exact source authentication remains Mathlib-free; this
companion checks every dyadic reduction, finite sum, tail, and source endpoint.
-/

namespace Hex.Interval.Experiment.PntLogRational

open Finset
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

/-- Dyadic/atanh enclosure for a positive real input. -/
theorem rationalRangeWindow (input : ℝ) (shift : Nat) (x lower upper : ℝ)
    (hxLower : 0 ≤ x) (hxUpper : x < 1)
    (identity : input = (2 : ℝ) ^ shift * ((1 + x) / (1 - x)))
    (lowerCheck : lower < shift * (0.6931471803 : ℝ) +
      PntLogNatural.partialSum x 8)
    (upperCheck : shift * (0.6931471808 : ℝ) +
      PntLogNatural.partialSum x 8 + PntLogNatural.tailBound x 8 < upper) :
    lower < Real.log input ∧ Real.log input < upper := by
  have ratioPositive : 0 < (1 + x) / (1 - x) :=
    div_pos (by linarith) (by linarith)
  have logIdentity : Real.log input =
      shift * Real.log 2 + Real.log ((1 + x) / (1 - x)) := by
    rw [identity, Real.log_mul (by positivity) ratioPositive.ne']
    rw [Real.log_pow]
  rw [logIdentity]
  constructor
  · have series := PntLogNatural.partialSum_le_logRatio hxLower hxUpper 8
    nlinarith [Real.log_two_gt_d9]
  · have series := PntLogNatural.logRatio_le_sumTail hxLower hxUpper 8
    nlinarith [Real.log_two_lt_d9]

/-- One reusable theorem checks all fifteen exact source records. -/
theorem certificateWindow (value : Certificate)
    (accepted : rowFor? value.sourceIndex = some value) :
    (value.lower / 10 ^ value.scale : ℝ) <
        Real.log (value.inputNumerator / value.inputDenominator) ∧
      Real.log (value.inputNumerator / value.inputDenominator) <
        (value.upper / 10 ^ value.scale : ℝ) := by
  let input : ℝ := value.inputNumerator / value.inputDenominator
  let x : ℝ := value.xNumerator / value.xDenominator
  let shift := value.shift
  have member : value ∈ rows := List.mem_of_find?_eq_some accepted
  simp [rows] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply rationalRangeWindow (input := input) (shift := shift) (x := x) <;>
    norm_num [input, x, shift, row2353, row32, row658, row11723, row5e10, row32e12,
      row130, row155, row200, row300, row550, row1500, row10000, row1e8,
      row3e10, PntLogRational.row, PntLogNatural.partialSum,
      PntLogNatural.tailBound, Finset.sum_range_succ]

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .exact value, x => x = (value.numerator : ℝ) / value.denominator
  | .window value, x =>
      (value.lower / 10 ^ value.scale : ℝ) < x ∧
        x < (value.upper / 10 ^ value.scale : ℝ)
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

theorem logEntails (value : Certificate)
    (accepted : rowFor? value.sourceIndex = some value)
    (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (inputFacts : assumptions = [{ node := input, fact := .exact value.input }]) :
    semantics.Entails graph assumptions { node := output, fact := .window value.window } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  have inputExact : valuation input =
      (value.inputNumerator : ℝ) / value.inputDenominator := by
    exact holds { node := input, fact := .exact value.input } (by simp [inputFacts])
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = Real.log (valuation input) := by
    simpa [logModel, arguments, List.map] using related
  change Contains (.window value.window) (valuation output)
  rw [outputEq, inputExact]
  simpa [Contains, Certificate.window] using certificateWindow value accepted

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
      if proposed : context.proposed.fact = .window value.window then
        match found : context.program.node? context.proposed.node with
        | some instruction =>
            if operation : instruction.op = ({ index := 1 } : OpId) then
              match arguments : instruction.args with
              | [input] =>
                  if inputFacts : context.assumptions =
                      [{ node := input, fact := .exact value.input }] then
                    some
                      { proof := by
                          have proposedEq : context.proposed =
                              { node := context.proposed.node,
                                fact := .window value.window } :=
                            factWith context.proposed proposed
                          rw [proposedEq]
                          exact logEntails value accepted context.program context.assumptions
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
def logProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[factSchema] },
    emit := { schemas := [{ key := factSchema.key, handle := ``factSchema }] } }
def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) := #[sourceProof, logProof]

/-! Exact source-shaped wrappers for the coherent direct-logarithm family. -/

theorem log_2_353_gt : (0.855 : ℝ) < Real.log 2.353 := by
  have bound := (certificateWindow row2353 (by decide)).1
  simp only [row2353, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_3_2_gt : (1.163 : ℝ) < Real.log 3.2 := by
  have bound := (certificateWindow row32 (by decide)).1
  simp only [row32, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_6_58_gt : (1.884034 : ℝ) < Real.log 6.58 := by
  have bound := (certificateWindow row658 (by decide)).1
  simp only [row658, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound

theorem log_11723_lt : Real.log (11723 : ℝ) ≤ 937 / 100 := by
  have bound := (certificateWindow row11723 (by decide)).2.le
  simp only [row11723, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_5e10_gt : (24.6352888 : ℝ) ≤ Real.log 5e10 := by
  have bound := (certificateWindow row5e10 (by decide)).1.le
  simp only [row5e10, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_5e10_lt : Real.log 5e10 ≤ (24.6352889 : ℝ) := by
  have bound := (certificateWindow row5e10 (by decide)).2.le
  simp only [row5e10, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_32e12_gt : (31.0967570 : ℝ) ≤ Real.log 32e12 := by
  have bound := (certificateWindow row32e12 (by decide)).1.le
  simp only [row32e12, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_32e12_lt : Real.log 32e12 ≤ (31.0967571 : ℝ) := by
  have bound := (certificateWindow row32e12 (by decide)).2.le
  simp only [row32e12, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound

theorem log_130_lt : Real.log 130 < 4.868 := by
  have bound := (certificateWindow row130 (by decide)).2
  simp only [row130, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_155_lt : Real.log 155 < 5.044 := by
  have bound := (certificateWindow row155 (by decide)).2
  simp only [row155, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_200_lt : Real.log 200 < 5.299 := by
  have bound := (certificateWindow row200 (by decide)).2
  simp only [row200, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_300_lt : Real.log 300 < 5.704 := by
  have bound := (certificateWindow row300 (by decide)).2
  simp only [row300, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_550_lt : Real.log 550 < 6.310 := by
  have bound := (certificateWindow row550 (by decide)).2
  simp only [row550, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_1500_lt : Real.log 1500 < 7.314 := by
  have bound := (certificateWindow row1500 (by decide)).2
  simp only [row1500, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_10000_lt : Real.log 10000 < 9.211 := by
  have bound := (certificateWindow row10000 (by decide)).2
  simp only [row10000, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_1e8_lt : Real.log ((10 : ℝ) ^ 8) < 18.421 := by
  have bound := (certificateWindow row1e8 (by decide)).2
  simp only [row1e8, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound
theorem log_3e10_lt : Real.log (3 * (10 : ℝ) ^ 10) < 24.125 := by
  have bound := (certificateWindow row3e10 (by decide)).2
  simp only [row3e10, PntLogRational.row] at bound
  norm_num at bound ⊢
  exact bound

/-! Generic proof-frontend fixture at the large-shift `32e12` row. -/

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .exact row32e12.input },
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
  | ⟨0⟩ => 32000000000000
  | ⟨1⟩ => Real.log 32000000000000
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
      | succ index => simp [Program.node?, program] at found

theorem closeLog32e12
    (result : Evidence
      (semantics.Entails program baseFacts representativeInput.target)) :
    (31.0967570 : ℝ) < Real.log 32e12 ∧ Real.log 32e12 < 31.0967571 := by
  have closed := result.proof valuation valuationModels (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change Contains (.exact row32e12.input) (valuation (node 0))
      norm_num [Contains, Certificate.input, row32e12, PntLogRational.row,
        valuation, node]
    · trivial)
  change Contains (.window row32e12.window) (valuation (node 1)) at closed
  norm_num [Contains, Certificate.window, row32e12, PntLogRational.row,
    valuation, node] at closed ⊢
  exact closed

end Hex.Interval.Experiment.PntLogRational
