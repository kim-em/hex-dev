/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntLogNatural
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

namespace Hex.Interval.Experiment.PntLogNatural

open Finset
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

noncomputable def partialSum (x : ℝ) (terms : Nat) : ℝ :=
  ∑ k ∈ range terms, 2 * x ^ (2 * k + 1) / (2 * (k : ℝ) + 1)

noncomputable def tailBound (x : ℝ) (terms : Nat) : ℝ :=
  2 * x ^ (2 * terms + 1) / (1 - x ^ 2)

theorem partialSum_le_logRatio {x : ℝ} (lower : 0 ≤ x) (upper : x < 1)
    (terms : Nat) : partialSum x terms ≤ Real.log ((1 + x) / (1 - x)) := by
  have bound := Real.sum_range_le_log_div (x := x) lower upper terms
  have scaled := mul_le_mul_of_nonneg_left bound (by norm_num : (0 : ℝ) ≤ 2)
  calc
    partialSum x terms =
        2 * ∑ k ∈ range terms, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
      simp only [partialSum, mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    _ ≤ 2 * (1 / 2 * Real.log ((1 + x) / (1 - x))) := scaled
    _ = Real.log ((1 + x) / (1 - x)) := by ring

theorem logRatio_le_sumTail {x : ℝ} (lower : 0 ≤ x) (upper : x < 1)
    (terms : Nat) :
    Real.log ((1 + x) / (1 - x)) ≤ partialSum x terms + tailBound x terms := by
  have bound := Real.log_div_le_sum_range_add (x := x) lower upper terms
  have scaled := mul_le_mul_of_nonneg_left bound (by norm_num : (0 : ℝ) ≤ 2)
  calc
    Real.log ((1 + x) / (1 - x)) =
        2 * (1 / 2 * Real.log ((1 + x) / (1 - x))) := by ring
    _ ≤ 2 * ((∑ k ∈ range terms,
        x ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) +
          x ^ (2 * terms + 1) / (1 - x ^ 2)) := scaled
    _ = partialSum x terms + tailBound x terms := by
      rw [mul_add]
      congr 1
      · simp only [partialSum, mul_sum]
        apply sum_congr rfl
        intro k _
        ring
      · simp only [tailBound]
        ring

theorem rangeWindow (input shift : Nat) (x lower upper : ℝ)
    (hxLower : 0 ≤ x) (hxUpper : x < 1)
    (identity : (input : ℝ) = (2 : ℝ) ^ shift * ((1 + x) / (1 - x)))
    (lowerCheck : lower < shift * (0.6931471803 : ℝ) + partialSum x 8)
    (upperCheck : shift * (0.6931471808 : ℝ) +
      partialSum x 8 + tailBound x 8 < upper) :
    lower < Real.log input ∧ Real.log input < upper := by
  have ratioPositive : 0 < (1 + x) / (1 - x) :=
    div_pos (by linarith) (by linarith)
  have logIdentity : Real.log input =
      shift * Real.log 2 + Real.log ((1 + x) / (1 - x)) := by
    rw [identity, Real.log_mul (by positivity) ratioPositive.ne']
    rw [Real.log_pow]
  rw [logIdentity]
  constructor
  · have series := partialSum_le_logRatio hxLower hxUpper 8
    nlinarith [Real.log_two_gt_d9]
  · have series := logRatio_le_sumTail hxLower hxUpper 8
    nlinarith [Real.log_two_lt_d9]

theorem certificateWindow (row : Certificate)
    (accepted : rowFor? row.input = some row) :
    (row.lower / 10 ^ row.scale : ℝ) < Real.log row.input ∧
      Real.log row.input < (row.upper / 10 ^ row.scale : ℝ) := by
  let chosenShift := row.shift
  let chosenX : ℝ := row.xNum / row.xDen
  have member : row ∈ rows := List.mem_of_find?_eq_some accepted
  simp [rows] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals
    apply rangeWindow (shift := chosenShift) (x := chosenX) <;>
    norm_num [chosenShift, chosenX, row3, row5, row7, row10, row11, row13,
      row17, row19, row23, row29, row30, row32, PntLogNatural.row,
      partialSum, tailBound, Finset.sum_range_succ]

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .exact value, x => x = value
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

theorem logEntails (row : Certificate) (accepted : rowFor? row.input = some row)
    (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (inputFacts : assumptions = [{ node := input, fact := .exact row.input }]) :
    semantics.Entails graph assumptions { node := output, fact := .window row.window } := by
  intro valuation model holds
  change NodeId → ℝ at valuation
  have inputExact : valuation input = (row.input : ℝ) := by
    exact holds { node := input, fact := .exact row.input } (by simp [inputFacts])
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = Real.log (valuation input) := by
    simpa [logModel, arguments, List.map] using related
  change Contains (.window row.window) (valuation output)
  rw [outputEq, inputExact]
  simpa [Contains, Certificate.window] using certificateWindow row accepted

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) : fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def factSchema : PackedFactSchema semantics where
  rule := ruleKey
  schema := 1
  Certificate := Certificate
  decode := decode?
  replay := fun _ _ context row =>
    if accepted : rowFor? row.input = some row then
      if proposed : context.proposed.fact = .window row.window then
        match found : context.program.node? context.proposed.node with
        | some instruction =>
            if operation : instruction.op = ({ index := 1 } : OpId) then
              match arguments : instruction.args with
              | [input] =>
                  if inputFacts : context.assumptions =
                      [{ node := input, fact := .exact row.input }] then
                    some
                      { proof := by
                          have proposedEq : context.proposed =
                              { node := context.proposed.node,
                                fact := .window row.window } :=
                            factWith context.proposed proposed
                          rw [proposedEq]
                          exact logEntails row accepted context.program context.assumptions
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

/-! Source-shaped wrappers for the complete natural-number subtable. -/

private theorem log3Bounds :
    (1.098612 : ℝ) < Real.log 3 ∧ Real.log 3 < 1.098613 := by
  have result := certificateWindow row3 (by decide)
  norm_num [row3, PntLogNatural.row] at result ⊢
  exact result
private theorem log5Bounds :
    (1.609437 : ℝ) < Real.log 5 ∧ Real.log 5 < 1.609438 := by
  have result := certificateWindow row5 (by decide)
  norm_num [row5, PntLogNatural.row] at result ⊢
  exact result
private theorem log7Bounds :
    (1.945910 : ℝ) < Real.log 7 ∧ Real.log 7 < 1.945911 := by
  have result := certificateWindow row7 (by decide)
  norm_num [row7, PntLogNatural.row] at result ⊢
  exact result
private theorem log10Bounds :
    (2.302585 : ℝ) < Real.log 10 ∧ Real.log 10 < 2.302586 := by
  have result := certificateWindow row10 (by decide)
  norm_num [row10, PntLogNatural.row] at result ⊢
  exact result
private theorem log11Bounds :
    (2.397895 : ℝ) < Real.log 11 ∧ Real.log 11 < 2.397896 := by
  have result := certificateWindow row11 (by decide)
  norm_num [row11, PntLogNatural.row] at result ⊢
  exact result
private theorem log13Bounds :
    (2.564949 : ℝ) < Real.log 13 ∧ Real.log 13 < 2.564950 := by
  have result := certificateWindow row13 (by decide)
  norm_num [row13, PntLogNatural.row] at result ⊢
  exact result
private theorem log17Bounds :
    (2.833213 : ℝ) < Real.log 17 ∧ Real.log 17 < 2.833214 := by
  have result := certificateWindow row17 (by decide)
  norm_num [row17, PntLogNatural.row] at result ⊢
  exact result
private theorem log19Bounds :
    (2.944438 : ℝ) < Real.log 19 ∧ Real.log 19 < 2.944439 := by
  have result := certificateWindow row19 (by decide)
  norm_num [row19, PntLogNatural.row] at result ⊢
  exact result
private theorem log23Bounds :
    (3.135494 : ℝ) < Real.log 23 ∧ Real.log 23 < 3.135495 := by
  have result := certificateWindow row23 (by decide)
  norm_num [row23, PntLogNatural.row] at result ⊢
  exact result
private theorem log29Bounds :
    (3.367295 : ℝ) < Real.log 29 ∧ Real.log 29 < 3.367296 := by
  have result := certificateWindow row29 (by decide)
  norm_num [row29, PntLogNatural.row] at result ⊢
  exact result
private theorem log30Bounds :
    (3.401197 : ℝ) < Real.log 30 ∧ Real.log 30 < 3.401198 := by
  have result := certificateWindow row30 (by decide)
  norm_num [row30, PntLogNatural.row] at result ⊢
  exact result
private theorem log32Bounds :
    (3.465735 : ℝ) < Real.log 32 ∧ Real.log 32 < 3.465736 := by
  have result := certificateWindow row32 (by decide)
  norm_num [row32, PntLogNatural.row] at result ⊢
  exact result

theorem log_3_gt : (1.098612 : ℝ) < Real.log 3 := log3Bounds.1
theorem log_3_lt : Real.log 3 < (1.098613 : ℝ) := log3Bounds.2
theorem log_5_gt : (1.609437 : ℝ) < Real.log 5 := log5Bounds.1
theorem log_5_lt : Real.log 5 < (1.609438 : ℝ) := log5Bounds.2
theorem log_7_gt : (1.945910 : ℝ) < Real.log 7 := log7Bounds.1
theorem log_7_lt : Real.log 7 < (1.945911 : ℝ) := log7Bounds.2
theorem log_10_gt : (2.302585 : ℝ) < Real.log 10 := log10Bounds.1
theorem log_10_lt : Real.log 10 < (2.302586 : ℝ) := log10Bounds.2
theorem log_11_gt : (2.397895 : ℝ) < Real.log 11 := log11Bounds.1
theorem log_11_lt : Real.log 11 < (2.397896 : ℝ) := log11Bounds.2
theorem log_13_gt : (2.564949 : ℝ) < Real.log 13 := log13Bounds.1
theorem log_13_lt : Real.log 13 < (2.564950 : ℝ) := log13Bounds.2
theorem log_17_gt : (2.833213 : ℝ) < Real.log 17 := log17Bounds.1
theorem log_17_lt : Real.log 17 < (2.833214 : ℝ) := log17Bounds.2
theorem log_19_gt : (2.944438 : ℝ) < Real.log 19 := log19Bounds.1
theorem log_19_lt : Real.log 19 < (2.944439 : ℝ) := log19Bounds.2
theorem log_23_gt : (3.135494 : ℝ) < Real.log 23 := log23Bounds.1
theorem log_23_lt : Real.log 23 < (3.135495 : ℝ) := log23Bounds.2
theorem log_29_gt : (3.367295 : ℝ) < Real.log 29 := log29Bounds.1
theorem log_29_lt : Real.log 29 < (3.367296 : ℝ) := log29Bounds.2
theorem log_30_gt : (3.401197 : ℝ) < Real.log 30 := log30Bounds.1
theorem log_30_lt : Real.log 30 < (3.401198 : ℝ) := log30Bounds.2
theorem log_32_gt : (3.465735 : ℝ) < Real.log 32 := log32Bounds.1
theorem log_32_lt : Real.log 32 < (3.465736 : ℝ) := log32Bounds.2

/-! Generic proof-frontend fixture at representative row 29; row 30 has the
worst reduced ratio among the rows. -/

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .exact row29.input },
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
  | ⟨0⟩ => 29
  | ⟨1⟩ => Real.log 29
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

theorem closeLog29
    (result : Evidence
      (semantics.Entails program baseFacts representativeInput.target)) :
    (3.367295 : ℝ) < Real.log 29 ∧ Real.log 29 < 3.367296 := by
  have closed := result.proof valuation valuationModels (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rfl
    · trivial)
  change Contains (.window row29.window) (valuation (node 1)) at closed
  norm_num [Contains, Certificate.window, row29, PntLogNatural.row, valuation,
    node] at closed ⊢
  exact closed

end Hex.Interval.Experiment.PntLogNatural
