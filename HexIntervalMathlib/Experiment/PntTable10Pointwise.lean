/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntTable10Shard
public import HexInterval.Experiment.PntTable10Pointwise

@[expose] public section

/-!
# Ordinary-kernel semantics for the BKLNW Table 10 pointwise-row batch

The runtime payload's ten rational checks are lifted through the exponential
base bounds proved for the row-25 shard.  This proves the exact single numeric
premise consumed by PNT+'s pointwise reduction for rows 90 and 95.
-/

namespace Hex.Interval.Experiment.PntTable10Pointwise

open Real Set Finset
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics
open PntTable10Shard

theorem decimalPowValue (value : Decimal) (power : Nat) :
    (decimalPow value power).value = value.value ^ power := by
  unfold decimalPow Decimal.value decimal
  push_cast
  rw [pow_mul, div_pow]

/-- The left side of pinned PNT+ `row_bound_pointwise`'s sole numeric
premise. -/
noncomputable def premise (value : RowCertificate) (column : Nat) : ℝ :=
  value.a1.value * value.nextRow ^ column * Real.exp (-(1 / 2 * value.row)) +
    value.a2.value * value.nextRow ^ column * Real.exp (-(2 / 3 * value.row)) +
      value.epsilon.value * value.nextRow ^ column

def rowCells : List (RowCertificate × Cell) :=
  rows.flatMap fun value => value.cells.map fun cell => (value, cell)

noncomputable def endpointValues : List ℝ :=
  rowCells.map fun pair => premise pair.1 pair.2.coordinate.column

private theorem endpointApprox (value : RowCertificate) (cell : Cell)
    (positive : value.row ≠ 0) :
    premise value cell.coordinate.column ≤ (endpoint value cell).value := by
  have windows := expTermsUpper value.row positive
  have halfValue : halfBase.value = (0.606530660 : ℝ) := by
    norm_num [halfBase, Decimal.value, decimal]
  have twoThirdValue : twoThirdBase.value = (0.513417120 : ℝ) := by
    norm_num [twoThirdBase, Decimal.value, decimal]
  have halfWindow : Real.exp (-(1 / 2 * (value.row : ℝ))) ≤
      (0.606530660 : ℝ) ^ value.row := by
    simpa [div_eq_mul_inv, mul_comm] using windows.1.le
  have twoThirdWindow : Real.exp (-(2 / 3 * (value.row : ℝ))) ≤
      (0.513417120 : ℝ) ^ value.row := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using windows.2.le
  unfold premise endpoint
  simp only [decimalMulValue, decimalAddValue]
  rw [decimalPowNatValue, decimalPowValue, decimalPowValue]
  calc
    _ ≤ value.a1.value * (value.nextRow : ℝ) ^ cell.coordinate.column *
          (0.606530660 : ℝ) ^ value.row +
        value.a2.value * (value.nextRow : ℝ) ^ cell.coordinate.column *
          (0.513417120 : ℝ) ^ value.row +
        value.epsilon.value * (value.nextRow : ℝ) ^ cell.coordinate.column := by
      apply add_le_add
      · apply add_le_add
        · apply mul_le_mul_of_nonneg_left halfWindow
          unfold Decimal.value
          positivity
        · apply mul_le_mul_of_nonneg_left twoThirdWindow
          unfold Decimal.value
          positivity
      · exact le_rfl
    _ = _ := by rw [halfValue, twoThirdValue]; ring

private theorem pairParts (value : RowCertificate) (cell : Cell)
    (member : (value, cell) ∈ rowCells) : value ∈ rows ∧ cell ∈ value.cells := by
  rw [rowCells, List.mem_flatMap] at member
  obtain ⟨sourceRow, rowMember, pairMember⟩ := member
  rw [List.mem_map] at pairMember
  obtain ⟨sourceCell, cellMember, pairEq⟩ := pairMember
  have rowEq : sourceRow = value := congrArg Prod.fst pairEq
  have cellEq : sourceCell = cell := congrArg Prod.snd pairEq
  subst sourceRow
  subst sourceCell
  exact ⟨rowMember, cellMember⟩

private theorem rowPositive (value : RowCertificate) (member : value ∈ rows) :
    value.row ≠ 0 := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> norm_num [row90, row95, rowCertificate]

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
private theorem sourceChecked (value : RowCertificate) (cell : Cell)
    (rowMember : value ∈ rows) (cellMember : cell ∈ value.cells) :
    checkCell value cell = true := by
  have valid : rows.all (fun row => row.cells.all (checkCell row)) = true := by decide
  rw [List.all_eq_true] at valid
  have rowValid := valid value rowMember
  rw [List.all_eq_true] at rowValid
  exact rowValid cell cellMember

/-- Every authenticated coordinate proves the exact numeric premise used by
the pinned pointwise reduction. -/
theorem rowCell (value : RowCertificate) (cell : Cell)
    (member : (value, cell) ∈ rowCells) :
    premise value cell.coordinate.column ≤ cell.target.value := by
  obtain ⟨rowMember, cellMember⟩ := pairParts value cell member
  have checked := sourceChecked value cell rowMember cellMember
  rw [checkCell] at checked
  simp only [Bool.and_eq_true] at checked
  exact (endpointApprox value cell (rowPositive value rowMember)).trans
    ((decimalLe_iff _ _).mp checked.2)

abbrev SourceTuple := ℝ × ℝ × ℝ × ℝ × ℝ × ℝ

noncomputable def sourceTuple (value : RowCertificate) : SourceTuple :=
  (value.row, value.cell1.listed.value, value.cell2.listed.value,
    value.cell3.listed.value, value.cell4.listed.value, value.cell5.listed.value)

/-- The exact tuples at pinned `BKLNW_tables.lean:839-840`. -/
noncomputable def sourceTable : List SourceTuple := rows.map sourceTuple

private theorem sourceValues (value : RowCertificate) (rowMember : value ∈ rows)
    (B : Nat → ℝ)
    (member : ((value.row : ℝ), B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    B 1 = value.cell1.listed.value ∧ B 2 = value.cell2.listed.value ∧
      B 3 = value.cell3.listed.value ∧ B 4 = value.cell4.listed.value ∧
      B 5 = value.cell5.listed.value := by
  rw [sourceTable, List.mem_map] at member
  obtain ⟨observed, observedMember, tupleEq⟩ := member
  have rowEq : observed.row = value.row := by
    have realEq := congrArg Prod.fst tupleEq
    have : (observed.row : ℝ) = value.row := by simpa [sourceTuple] using realEq
    exact_mod_cast this
  have observedEq : observed = value := by
    simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at observedMember rowMember
    rcases observedMember with rfl | rfl <;> rcases rowMember with rfl | rfl
    all_goals norm_num [row90, row95, rowCertificate] at rowEq
    all_goals rfl
  subst observed
  have h1 := congrArg (fun tuple : SourceTuple => tuple.2.1) tupleEq
  have h2 := congrArg (fun tuple : SourceTuple => tuple.2.2.1) tupleEq
  have h3 := congrArg (fun tuple : SourceTuple => tuple.2.2.2.1) tupleEq
  have h4 := congrArg (fun tuple : SourceTuple => tuple.2.2.2.2.1) tupleEq
  have h5 := congrArg (fun tuple : SourceTuple => tuple.2.2.2.2.2) tupleEq
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm⟩

private theorem cellPair (value : RowCertificate) (rowMember : value ∈ rows)
    (cell : Cell) (cellMember : cell ∈ value.cells) : (value, cell) ∈ rowCells := by
  rw [rowCells, List.mem_flatMap]
  exact ⟨value, rowMember, by simpa using cellMember⟩

private structure SourceShape (value : RowCertificate) : Prop where
  cell1 : value.cell1.coordinate.column = 1 ∧
    value.cell1.target = corrected value.cell1.listed
  cell2 : value.cell2.coordinate.column = 2 ∧
    value.cell2.target = corrected value.cell2.listed
  cell3 : value.cell3.coordinate.column = 3 ∧
    value.cell3.target = corrected value.cell3.listed
  cell4 : value.cell4.coordinate.column = 4 ∧
    value.cell4.target = corrected value.cell4.listed
  cell5 : value.cell5.coordinate.column = 5 ∧
    value.cell5.target = corrected value.cell5.listed

private theorem sourceShape (value : RowCertificate) (member : value ∈ rows) :
    SourceShape value := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Source-dispatch-shaped replacement for all ten numeric premises in pinned
rows 90 and 95.  PNT+ may locally replace the decimal tactic call while
retaining its coefficient lemmas and `row_bound_pointwise` theorem. -/
theorem rowOfMem (value : RowCertificate) (rowMember : value ∈ rows) (B : Nat → ℝ)
    (member : ((value.row : ℝ), B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    ∀ k ∈ Finset.Icc 1 5, premise value k ≤ B k * margin.value := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sourceValues value rowMember B member
  have shape := sourceShape value rowMember
  intro k hk
  simp only [Finset.mem_Icc] at hk
  obtain ⟨lower, upper⟩ := hk
  interval_cases k
  · simpa only [shape.cell1.1, shape.cell1.2, corrected, decimalMulValue, h1]
      using rowCell value value.cell1
        (cellPair value rowMember value.cell1 (by simp [RowCertificate.cells]))
  · simpa only [shape.cell2.1, shape.cell2.2, corrected, decimalMulValue, h2]
      using rowCell value value.cell2
        (cellPair value rowMember value.cell2 (by simp [RowCertificate.cells]))
  · simpa only [shape.cell3.1, shape.cell3.2, corrected, decimalMulValue, h3]
      using rowCell value value.cell3
        (cellPair value rowMember value.cell3 (by simp [RowCertificate.cells]))
  · simpa only [shape.cell4.1, shape.cell4.2, corrected, decimalMulValue, h4]
      using rowCell value value.cell4
        (cellPair value rowMember value.cell4 (by simp [RowCertificate.cells]))
  · simpa only [shape.cell5.1, shape.cell5.2, corrected, decimalMulValue, h5]
      using rowCell value value.cell5
        (cellPair value rowMember value.cell5 (by simp [RowCertificate.cells]))

def sourceModel : OperationSemantics.Model ℝ :=
  { operation := sourceOperation, relation := fun inputs _ => inputs = [] }

def batchModel : OperationSemantics.Model ℝ :=
  { operation := batchOperation, relation := fun inputs _ => inputs = endpointValues }

def operationModels : Array (OperationSemantics.Model ℝ) := #[sourceModel, batchModel]

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .upper cell, value => value ≤ cell.target.value
  | .empty, _ => False

def semantics : Semantics Bound := OperationSemantics.semantics operationModels Contains

def boundSchema : FactDomainSchema semantics where
  top := fun _ => .all
  topSound := by intros; trivial
  proveMeet := fun _ _ previous proposed installed =>
    if exact : installed = previous.meet proposed then
      some
        { proof := by
            subst installed
            intro valuation _
            exact PntTable10Shard.containsMeet previous proposed (valuation _) }
    else none

def laws : Laws semantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change Contains fact (valuation left) ↔ Contains fact (valuation right)
      rw [values] }

private theorem mappedBounds (pairs : List (RowCertificate × Cell))
    (bounded : ∀ pair ∈ pairs,
      premise pair.1 pair.2.coordinate.column ≤ pair.2.target.value) :
    List.Forall₂ (fun value cell => value ≤ cell.target.value)
      (pairs.map fun pair => premise pair.1 pair.2.coordinate.column)
      (pairs.map Prod.snd) := by
  induction pairs with
  | nil => exact .nil
  | cons pair remaining induction =>
      exact .cons (bounded pair (by simp))
        (induction fun current member => bounded current (by simp [member]))

private theorem endpointValuesBound :
    List.Forall₂ (fun value cell => value ≤ cell.target.value) endpointValues cells := by
  have cellsEq : cells = rowCells.map Prod.snd := by
    simp [cells, rowCells, rows, RowCertificate.cells]
  rw [cellsEq]
  exact mappedBounds rowCells fun pair member => rowCell pair.1 pair.2 member

private theorem forall₂_right_get? {relation : α → β → Prop}
    {left : List α} {right : List β} (related : List.Forall₂ relation left right)
    (index : Nat) (value : β) (found : right[index]? = some value) :
    ∃ input, left[index]? = some input ∧ relation input value := by
  induction index generalizing left right with
  | zero =>
      cases related with
      | nil => simp at found
      | cons head tail => simp at found; subst value; exact ⟨_, by simp, head⟩
  | succ index induction =>
      cases related with
      | nil => simp at found
      | cons head tail => simp at found ⊢; exact induction tail found

private theorem cellEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (anchor : NodeId) (instruction : Node) (target : NodeId) (cell : Cell) (index : Nat)
    (found : graph.node? anchor = some instruction)
    (operation : instruction.op = { index := 1 })
    (targetFound : instruction.args[index]? = some target)
    (cellFound : cells[index]? = some cell) (_noAssumptions : assumptions = []) :
    semantics.Entails graph assumptions { node := target, fact := .upper cell } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions → Contains assumption.fact (valuation assumption.node)) →
      Contains (.upper cell) (valuation target)
  intro valuation models _
  obtain ⟨meaning, meaningAt, related⟩ := models.2 anchor instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have values : instruction.args.map valuation = endpointValues := related
  obtain ⟨input, inputFound, inputBound⟩ :=
    forall₂_right_get? endpointValuesBound index cell cellFound
  have mappedTarget : (instruction.args.map valuation)[index]? = some (valuation target) := by
    simp [targetFound]
  have targetValue : endpointValues[index]? = some (valuation target) := by
    rw [← values]
    exact mappedTarget
  have targetInput : valuation target = input :=
    Option.some.inj (targetValue.symm.trans inputFound)
  change valuation target ≤ cell.target.value
  simpa [targetInput] using inputBound

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) : fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def batchFactSchema : PackedFactSchema semantics where
  rule := ruleKey
  schema := 1
  Certificate := Unit
  decode := decodeBatch?
  replay := fun _ action context _ =>
    match found : context.program.node? action.node with
    | some instruction =>
        if operation : instruction.op = ({ index := 1 } : OpId) then
          if noAssumptions : context.assumptions = [] then
            match proposedFact : context.proposed.fact with
            | .upper cell =>
                let index := context.proposed.node.index
                match cellFound : cells[index]? with
                | some expected =>
                    if cellExact : cell = expected then
                      if targetFound : instruction.args[index]? = some context.proposed.node then
                        some
                          { proof := by
                              subst expected
                              have proposedEq : context.proposed =
                                  { node := context.proposed.node, fact := .upper cell } :=
                                factWith context.proposed proposedFact
                              rw [proposedEq]
                              exact cellEntails context.program context.assumptions action.node
                                instruction context.proposed.node cell index found operation
                                targetFound cellFound noAssumptions }
                      else none
                    else none
                | none => none
            | .all | .empty => none
          else none
        else none
    | none => none

def stableLaw : StableLaw semantics := OperationSemantics.stableLaw operationModels Contains

def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }, emit := { schemas := [] } }

def batchEmit : EmitPackage Lean.Name :=
  { schemas := [{ key := batchFactSchema.key, handle := ``batchFactSchema }] }

def batchProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[batchFactSchema] }, emit := batchEmit }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, batchProof]

end Hex.Interval.Experiment.PntTable10Pointwise
