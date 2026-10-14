/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntFks2Shard
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Checked semantics for the FKS2 shard probe

One Taylor remainder theorem serves all 1,000 cells.  Each generated rational
leaf authenticates its source endpoints, square-root enclosure, and final
split-exponential comparison exactly.
-/

namespace Hex.Interval.Experiment.PntFks2Shard

open Finset Real
open Propagator SemanticReplay OperationSemantics

noncomputable def Q.value (value : Q) : ℝ := value

theorem qLe_iff (left right : Q) :
    qLe left right = true ↔ left.value ≤ right.value := by
  simp only [qLe, decide_eq_true_eq, Q.value, Rat.cast_le]
  exact (Rat.le_iff left right).symm

theorem qLt_iff (left right : Q) :
    qLt left right = true ↔ left.value < right.value := by
  simp only [qLt, decide_eq_true_eq, Q.value, Rat.cast_lt]
  exact (Rat.lt_iff left right).symm

theorem qadd_value (left right : Q) :
    (qadd left right).value = left.value + right.value := by
  simp [qadd, Q.value, Rational.add_eq]

theorem qmul_value (left right : Q) :
    (qmul left right).value = left.value * right.value := by
  simp [qmul, Q.value, Rational.mul_eq]

theorem divInt_value (numerator denominator : Int) :
    Q.value (Rat.divInt numerator denominator) =
      (numerator : ℝ) / (denominator : ℝ) := by
  simp [Q.value, Rat.cast_divInt]

theorem qpow_value (value : Q) (degree : Nat) :
    (qpow value degree).value = value.value ^ degree := by
  induction degree with
  | zero => simp [qpow, Q.value]
  | succ degree induction =>
      simp [qpow, qmul_value, induction, pow_succ]

theorem qpow128_value (value : Q) :
    (qpow128 value).value = value.value ^ (128 : Nat) := by
  simp only [qpow128, qmul_value]
  ring

theorem factorial_eq (degree : Nat) : factorial degree = degree.factorial := by
  induction degree with
  | zero => rfl
  | succ degree induction => simp [factorial, Nat.factorial, induction]

theorem term_value (value : Q) (degree : Nat) :
    (term value degree).value = value.value ^ degree / degree.factorial := by
  rw [term, qmul_value, qpow_value, factorial_eq]
  rw [divInt_value]
  simp [div_eq_mul_inv]

theorem sumTerms_value (value : Q) (count : Nat) :
    (sumTerms value count).value =
      ∑ degree ∈ Finset.range count, value.value ^ degree / degree.factorial := by
  induction count with
  | zero => simp [sumTerms, Q.value]
  | succ count induction =>
      rw [sumTerms, qadd_value, induction, sum_range_succ, term_value]

theorem taylorUpper_value (value : Q) :
    (taylorUpper value).value =
      (∑ degree ∈ Finset.range 12,
        value.value ^ degree / degree.factorial) +
      value.value ^ 12 * (13 / ((12 : Nat).factorial * 12) : ℝ) := by
  rw [taylorUpper, qadd_value, sumTerms_value, qmul_value, qpow_value]
  rw [divInt_value]
  norm_num [Q.value, factorial_eq]

/-- The shared analytic provider: all per-cell work after this theorem is
exact rational arithmetic. -/
theorem exp_le_taylorUpper (value : Q)
    (nonnegative : 0 ≤ value.value) (atMostOne : value.value ≤ 1) :
    Real.exp value.value ≤ (taylorUpper value).value := by
  rw [taylorUpper_value]
  have bound := Real.exp_bound' nonnegative atMostOne (n := 12) (by norm_num)
  convert bound using 1
  all_goals ring

noncomputable def Cell.margin (cell : Cell) : ℝ :=
  aq.value * cell.slo.value ^ 3 -
    cell.eps.value * Real.exp ((2119 / 2500 : ℝ) * cell.shi.value)

def CellHolds (cell : Cell) : Prop :=
  ∀ s ∈ Set.Icc cell.slo.value cell.shi.value,
    Real.exp ((2119 / 2500 : ℝ) * s) ≤
      aq.value / cell.eps.value * s ^ 3

private theorem splitIdentity (cell : Cell) :
    (128 : ℝ) * (qmul cq128 cell.shi).value =
      (2119 / 2500 : ℝ) * cell.shi.value := by
  rw [qmul_value]
  norm_num [cq128, Q.value]
  ring

theorem margin_nonnegative_of_check (cell : Cell) (checked : checkCell cell = true) :
    0 ≤ cell.margin := by
  simp only [checkCell, Bool.and_eq_true, qLt_iff, qLe_iff] at checked
  obtain ⟨⟨⟨⟨⟨positive, sloNonnegative⟩, _sloLeShi⟩, _sloSquare⟩,
    _shiSquare⟩, reducedAtMostOne, final⟩ := checked
  have epsPositive : 0 < cell.eps.value := by simpa [Q.value] using positive
  have sloNonnegative' : 0 ≤ cell.slo.value := by
    simpa [Q.value] using sloNonnegative
  have reducedAtMostOne' : (qmul cq128 cell.shi).value ≤ 1 := by
    simpa [Q.value] using reducedAtMostOne
  have shiNonnegative : 0 ≤ cell.shi.value := le_trans sloNonnegative' _sloLeShi
  let reduced := qmul cq128 cell.shi
  have reducedNonnegative : 0 ≤ reduced.value := by
    dsimp [reduced]
    rw [qmul_value]
    have coefficient : 0 ≤ cq128.value := by norm_num [cq128, Q.value]
    exact mul_nonneg coefficient shiNonnegative
  have Taylor := exp_le_taylorUpper reduced reducedNonnegative reducedAtMostOne'
  have power := pow_le_pow_left₀ (Real.exp_pos _).le Taylor 128
  rw [← Real.exp_nat_mul] at power
  have split : ((128 : Nat) : ℝ) * reduced.value =
      (2119 / 2500 : ℝ) * cell.shi.value := by
    simpa [reduced] using splitIdentity cell
  rw [split] at power
  have epsNonnegative : 0 ≤ cell.eps.value := epsPositive.le
  have bounded := mul_le_mul_of_nonneg_left power epsNonnegative
  have finalReal :
      cell.eps.value * (qpow128 (taylorUpper reduced)).value ≤
        aq.value * (qpow cell.slo 3).value := by
    simpa [reduced, qmul_value] using final
  rw [qpow128_value, qpow_value] at finalReal
  unfold Cell.margin
  exact sub_nonneg.mpr (le_trans bounded finalReal)

theorem cellHolds_of_check (cell : Cell) (checked : checkCell cell = true) :
    CellHolds cell := by
  simp only [checkCell, Bool.and_eq_true, qLt_iff, qLe_iff] at checked
  have margin := margin_nonnegative_of_check cell (by
    simpa only [checkCell, Bool.and_eq_true, qLt_iff, qLe_iff] using checked)
  obtain ⟨⟨⟨⟨⟨positive, sloNonnegative⟩, sloLeShi⟩, _⟩, _⟩, _⟩ := checked
  have epsPositive : 0 < cell.eps.value := by simpa [Q.value] using positive
  have sloNonnegative' : 0 ≤ cell.slo.value := by
    simpa [Q.value] using sloNonnegative
  intro s hs
  have expMono :
      Real.exp ((2119 / 2500 : ℝ) * s) ≤
        Real.exp ((2119 / 2500 : ℝ) * cell.shi.value) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hs.2 (by norm_num)
  have cubeMono : cell.slo.value ^ 3 ≤ s ^ 3 := by
    exact pow_le_pow_left₀ sloNonnegative' hs.1 3
  have aqNonnegative : 0 ≤ aq.value := by norm_num [aq, Q.value]
  have endpoint :
      cell.eps.value *
          Real.exp ((2119 / 2500 : ℝ) * cell.shi.value) ≤
        aq.value * cell.slo.value ^ 3 := by
    unfold Cell.margin at margin
    linarith
  conv_rhs => rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ epsPositive).mpr
  calc
    Real.exp ((2119 / 2500 : ℝ) * s) * cell.eps.value
        = cell.eps.value * Real.exp ((2119 / 2500 : ℝ) * s) := by ring
    _ ≤ cell.eps.value * Real.exp ((2119 / 2500 : ℝ) * cell.shi.value) :=
      mul_le_mul_of_nonneg_left expMono epsPositive.le
    _ ≤ aq.value * cell.slo.value ^ 3 := endpoint
    _ ≤ aq.value * s ^ 3 := mul_le_mul_of_nonneg_left cubeMono aqNonnegative

/-- The exact rational obligations authenticated for each source cell. The
square conditions retain both source square-root endpoint checks. -/
def CellValid (cell : Cell) : Prop :=
  (((((Q.value 0 < cell.eps.value ∧ Q.value 0 ≤ cell.slo.value) ∧
    cell.slo.value ≤ cell.shi.value) ∧
    (qmul cell.slo cell.slo).value ≤ Q.value cell.b) ∧
    Q.value cell.b' ≤ (qmul cell.shi cell.shi).value) ∧
    (qmul cq128 cell.shi).value ≤ Q.value 1 ∧
    (qmul cell.eps (qpow128 (taylorUpper (qmul cq128 cell.shi)))).value ≤
      (qmul aq (qpow cell.slo 3)).value)

theorem check_of_valid (cell : Cell) (valid : CellValid cell) :
    checkCell cell = true := by
  simp only [checkCell, Bool.and_eq_true, qLt_iff, qLe_iff]
  simpa only [CellValid] using valid

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem chunk_valid (index : Nat) (valid : index < chunkCount)
    (cell : Cell) (member : cell ∈ chunk index) : CellValid cell := by
  norm_num [chunkCount] at valid
  interval_cases index <;>
    simp only [chunk, cellChunk, List.mem_cons, List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [CellValid, qmul_value, qpow_value, qpow128_value,
      taylorUpper_value] <;>
    norm_num [Q.value, cq128, aq]

/-- Exact source-shaped executable check for all 1,000 pinned cells. The fifty
bounded kernel checks evaluate the package-owned rational predicate; no native
evaluator or PNT+/LeanCert theorem is imported. -/
theorem cells11_checked : cells11.all checkCell = true := by
  exact List.all_eq_true.mpr fun cell member => by
    rw [cells11, List.mem_flatMap] at member
    obtain ⟨index, indexMember, cellMember⟩ := member
    exact check_of_valid cell (chunk_valid index (List.mem_range.mp indexMember)
      cell (by simpa [chunk] using cellMember))

/-- Arbitrary-membership semantic wrapper for the complete pinned shard. -/
theorem cells11_holds (cell : Cell) (member : cell ∈ cells11) : CellHolds cell :=
  cellHolds_of_check cell (List.all_eq_true.mp cells11_checked cell member)

/-! ## Indexed semantic replay for the fifty runtime chunks -/

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .nonnegative, value => 0 ≤ value

noncomputable def cellMargins : List ℝ := cells11.map Cell.margin

def sourceModel : OperationSemantics.Model ℝ :=
  { operation := sourceOperation, relation := fun inputs _ => inputs = [] }

def batchModel : OperationSemantics.Model ℝ :=
  { operation := batchOperation, relation := fun inputs _ => inputs = cellMargins }

def operationModels : Array (OperationSemantics.Model ℝ) := #[sourceModel, batchModel]
def semantics : Semantics Bound := OperationSemantics.semantics operationModels Contains

private theorem marginsForall (cells : List Cell)
    (checked : ∀ cell ∈ cells, checkCell cell = true) :
    List.Forall₂ (fun value (_ : Cell) => 0 ≤ value)
      (cells.map Cell.margin) cells := by
  induction cells with
  | nil => exact .nil
  | cons head tail induction =>
    exact .cons (margin_nonnegative_of_check head
        (checked head (by simp)))
        (induction (by
          intro cell member
          exact checked cell (by simp [member])))

theorem cellsMarginsNonnegative :
    List.Forall₂ (fun value (_ : Cell) => 0 ≤ value) cellMargins cells11 := by
  exact marginsForall cells11 (List.all_eq_true.mp cells11_checked)

private theorem forall₂_right_get? {relation : α → β → Prop}
    {left : List α} {right : List β} (related : List.Forall₂ relation left right)
    (index : Nat) (value : β) (found : right[index]? = some value) :
    ∃ input, left[index]? = some input ∧ relation input value := by
  induction index generalizing left right with
  | zero =>
      cases related with
      | nil => simp at found
      | cons head tail =>
          simp at found
          subst value
          exact ⟨_, by simp, head⟩
  | succ index induction =>
      cases related with
      | nil => simp at found
      | cons head tail =>
          simp at found ⊢
          exact induction tail found

private theorem marginEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (anchor : NodeId) (instruction : Node) (target : NodeId) (cell : Cell)
    (index : Nat) (found : graph.node? anchor = some instruction)
    (operation : instruction.op = ({ index := 1 } : OpId))
    (targetFound : instruction.args[index]? = some target)
    (cellFound : cells11[index]? = some cell) (_noAssumptions : assumptions = []) :
    semantics.Entails graph assumptions { node := target, fact := .nonnegative } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .nonnegative (valuation target)
  intro valuation models _
  obtain ⟨meaning, meaningAt, related⟩ := models.2 anchor instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have values : instruction.args.map valuation = cellMargins := by
    change instruction.args.map valuation = cellMargins at related
    exact related
  obtain ⟨input, inputFound, inputNonnegative⟩ :=
    forall₂_right_get? cellsMarginsNonnegative index cell cellFound
  have mappedTarget : (instruction.args.map valuation)[index]? =
      some (valuation target) := by simp [targetFound]
  have targetValue : cellMargins[index]? = some (valuation target) := by
    rw [← values]
    exact mappedTarget
  have targetInput : valuation target = input :=
    Option.some.inj (targetValue.symm.trans inputFound)
  simpa [Contains, targetInput] using inputNonnegative

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) : fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def batchFactSchema (chunkIndex : Nat) : PackedFactSchema semantics where
  rule := ruleKey chunkIndex
  schema := 1
  Certificate := Unit
  decode := decodeChunk? chunkIndex
  replay := fun _ action context _ =>
    match found : context.program.node? action.node with
    | some instruction =>
        if operation : instruction.op = ({ index := 1 } : OpId) then
          if noAssumptions : context.assumptions = [] then
            if writesExact : action.writes = chunkNodes chunkIndex then
              match proposedFact : context.proposed.fact with
              | .nonnegative =>
                  let index := context.proposed.node.index
                  match cellFound : cells11[index]? with
                  | some cell =>
                      if targetAllowed : (chunkNodes chunkIndex).contains context.proposed.node then
                        if targetFound : instruction.args[index]? = some context.proposed.node then
                          some
                            { proof := by
                                have proposedEq : context.proposed =
                                    { node := context.proposed.node,
                                      fact := .nonnegative } :=
                                  factWith context.proposed proposedFact
                                rw [proposedEq]
                                exact marginEntails context.program context.assumptions
                                  action.node instruction context.proposed.node cell index
                                  found operation targetFound cellFound noAssumptions }
                        else none
                      else none
                  | none => none
              | .all => none
            else none
          else none
        else none
    | none => none

end Hex.Interval.Experiment.PntFks2Shard
