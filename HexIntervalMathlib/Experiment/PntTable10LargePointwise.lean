/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntExpTail
public import HexIntervalMathlib.Experiment.PntTable10Shard
public import HexInterval.Experiment.PntTable10LargePointwise

@[expose] public section

/-!
# Ordinary-kernel semantics for the large-decimal Table 10 row

The checked `10^-100` tail is reused for both exponential terms at source row
`13800.7464`.  This avoids constructing enormous decimal powers while proving
the exact pointwise premise consumed by pinned PNT+.
-/

namespace Hex.Interval.Experiment.PntTable10LargePointwise

open Real Set Finset
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics
open PntTable10Shard

/-- The left side of pinned PNT+ `row_bound_pointwise`'s sole numeric premise. -/
noncomputable def premise (value : RowCertificate) (column : Nat) : ℝ :=
  value.a1.value * value.nextRow ^ column * Real.exp (-(1 / 2 * value.row.value)) +
    value.a2.value * value.nextRow ^ column * Real.exp (-(2 / 3 * value.row.value)) +
      value.epsilon.value * value.nextRow ^ column

noncomputable def endpointValues : List ℝ :=
  cells.map fun cell => premise certificate cell.coordinate.column

private theorem tailValue : certificate.tail.value = 1 / (10 : ℝ) ^ 100 := by
  norm_num [certificate, Decimal.value, decimal]

private theorem endpointApprox (cell : Cell) :
    premise certificate cell.coordinate.column ≤ (endpoint certificate cell).value := by
  have half : Real.exp (-(1 / 2 * certificate.row.value)) < 1 / (10 : ℝ) ^ 100 :=
    PntExpTail.tailOfUpper (by
      norm_num [certificate, Decimal.value, decimal])
  have twoThird : Real.exp (-(2 / 3 * certificate.row.value)) < 1 / (10 : ℝ) ^ 100 :=
    PntExpTail.tailOfUpper (by
      norm_num [certificate, Decimal.value, decimal])
  unfold premise endpoint
  simp only [decimalMulValue, decimalAddValue, decimalPowNatValue]
  calc
    _ ≤ certificate.a1.value * (certificate.nextRow : ℝ) ^ cell.coordinate.column *
          certificate.tail.value +
        certificate.a2.value * (certificate.nextRow : ℝ) ^ cell.coordinate.column *
          certificate.tail.value +
        certificate.epsilon.value * (certificate.nextRow : ℝ) ^ cell.coordinate.column := by
      rw [tailValue]
      apply add_le_add
      · apply add_le_add
        · apply mul_le_mul_of_nonneg_left half.le
          unfold Decimal.value
          positivity
        · apply mul_le_mul_of_nonneg_left twoThird.le
          unfold Decimal.value
          positivity
      · exact le_rfl
    _ = _ := by ring

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
private theorem sourceChecked (cell : Cell) (member : cell ∈ cells) :
    checkCell certificate cell = true := by
  have valid : certificate.cells.all (checkCell certificate) = true := by decide
  rw [List.all_eq_true] at valid
  exact valid cell member

/-- Every coordinate in the authenticated row proves the exact numeric
premise used by the pinned pointwise reduction. -/
theorem rowCell (cell : Cell) (member : cell ∈ cells) :
    premise certificate cell.coordinate.column ≤ cell.target.value := by
  have checked := sourceChecked cell member
  rw [checkCell] at checked
  simp only [Bool.and_eq_true] at checked
  exact (endpointApprox cell).trans ((decimalLe_iff _ _).mp checked.2)

abbrev SourceTuple := ℝ × ℝ × ℝ × ℝ × ℝ × ℝ

noncomputable def sourceTuple : SourceTuple :=
  (certificate.row.value, certificate.cell1.listed.value,
    certificate.cell2.listed.value, certificate.cell3.listed.value,
    certificate.cell4.listed.value, certificate.cell5.listed.value)

/-- The exact tuple at pinned `BKLNW_tables.lean:1067`. -/
noncomputable def sourceTable : List SourceTuple := [sourceTuple]

private theorem sourceValues (B : Nat → ℝ)
    (member : (certificate.row.value, B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    B 1 = certificate.cell1.listed.value ∧ B 2 = certificate.cell2.listed.value ∧
      B 3 = certificate.cell3.listed.value ∧ B 4 = certificate.cell4.listed.value ∧
      B 5 = certificate.cell5.listed.value := by
  simp only [sourceTable, List.mem_cons, List.not_mem_nil, or_false] at member
  have h1 := congrArg (fun tuple : SourceTuple => tuple.2.1) member
  have h2 := congrArg (fun tuple : SourceTuple => tuple.2.2.1) member
  have h3 := congrArg (fun tuple : SourceTuple => tuple.2.2.2.1) member
  have h4 := congrArg (fun tuple : SourceTuple => tuple.2.2.2.2.1) member
  have h5 := congrArg (fun tuple : SourceTuple => tuple.2.2.2.2.2) member
  exact ⟨by simpa [sourceTuple] using h1,
    by simpa [sourceTuple] using h2,
    by simpa [sourceTuple] using h3,
    by simpa [sourceTuple] using h4,
    by simpa [sourceTuple] using h5⟩

private structure SourceShape : Prop where
  cell1 : certificate.cell1.coordinate.column = 1 ∧
    certificate.cell1.target = corrected certificate.cell1.listed
  cell2 : certificate.cell2.coordinate.column = 2 ∧
    certificate.cell2.target = corrected certificate.cell2.listed
  cell3 : certificate.cell3.coordinate.column = 3 ∧
    certificate.cell3.target = corrected certificate.cell3.listed
  cell4 : certificate.cell4.coordinate.column = 4 ∧
    certificate.cell4.target = corrected certificate.cell4.listed
  cell5 : certificate.cell5.coordinate.column = 5 ∧
    certificate.cell5.target = corrected certificate.cell5.listed

private theorem sourceShape : SourceShape :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Source-dispatch-shaped replacement for all five numeric premises of pinned
row 13800.7464. PNT+ may retain its coefficient lemmas and
`row_bound_pointwise` theorem. -/
theorem rowOfMem (B : Nat → ℝ)
    (member : (certificate.row.value, B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    ∀ k ∈ Finset.Icc 1 5, premise certificate k ≤ B k * margin.value := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sourceValues B member
  have shape := sourceShape
  intro k hk
  simp only [Finset.mem_Icc] at hk
  obtain ⟨lower, upper⟩ := hk
  interval_cases k
  · simpa only [shape.cell1.1, shape.cell1.2, corrected, decimalMulValue, h1]
      using rowCell certificate.cell1 (by simp [cells, RowCertificate.cells])
  · simpa only [shape.cell2.1, shape.cell2.2, corrected, decimalMulValue, h2]
      using rowCell certificate.cell2 (by simp [cells, RowCertificate.cells])
  · simpa only [shape.cell3.1, shape.cell3.2, corrected, decimalMulValue, h3]
      using rowCell certificate.cell3 (by simp [cells, RowCertificate.cells])
  · simpa only [shape.cell4.1, shape.cell4.2, corrected, decimalMulValue, h4]
      using rowCell certificate.cell4 (by simp [cells, RowCertificate.cells])
  · simpa only [shape.cell5.1, shape.cell5.2, corrected, decimalMulValue, h5]
      using rowCell certificate.cell5 (by simp [cells, RowCertificate.cells])

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

private theorem mappedBounds (sourceCells : List Cell)
    (bounded : ∀ cell ∈ sourceCells,
      premise certificate cell.coordinate.column ≤ cell.target.value) :
    List.Forall₂ (fun value cell => value ≤ cell.target.value)
      (sourceCells.map fun cell => premise certificate cell.coordinate.column) sourceCells := by
  induction sourceCells with
  | nil => exact .nil
  | cons cell remaining induction =>
      exact .cons (bounded cell (by simp))
        (induction fun current member => bounded current (by simp [member]))

private theorem endpointValuesBound :
    List.Forall₂ (fun value cell => value ≤ cell.target.value) endpointValues cells :=
  mappedBounds cells fun cell member => rowCell cell member

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

end Hex.Interval.Experiment.PntTable10LargePointwise
