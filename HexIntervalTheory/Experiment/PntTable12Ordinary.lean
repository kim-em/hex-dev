/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntTable12Ordinary
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Checked semantics for the generated ordinary Table 12 batch

The four Taylor point windows are proved once.  Natural-power range reduction
then supplies every integer row, and exact rational arithmetic checks the five
source cuts for each row.  Replay uses one table payload and a uniform indexed
cell theorem; it has no row-specific proof schema.
-/

namespace Hex.Interval.Experiment.PntTable12Ordinary

open Finset
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

noncomputable def Decimal.value (decimal : Decimal) : ℝ :=
  decimal.mantissa / (10 : ℝ) ^ decimal.scale

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .upper cell, value => value ≤ cell.cut.value

theorem cutLe_iff (left right : CellCertificate) :
    left.cut.mantissa * 10 ^ right.cut.scale ≤
        right.cut.mantissa * 10 ^ left.cut.scale ↔
      left.cut.value ≤ right.cut.value := by
  unfold Decimal.value
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ left.cut.scale)
    (by positivity : (0 : ℝ) < 10 ^ right.cut.scale)]
  norm_cast

theorem containsMeet (left right : Bound) (value : ℝ) :
    Contains (left.meet right) value ↔
      Contains left value ∧ Contains right value := by
  cases left with
  | all => simp [Bound.meet, Contains]
  | upper left =>
      cases right with
      | all => simp [Bound.meet, Contains]
      | upper right =>
          simp only [Bound.meet]
          split <;> rename_i comparison
          · have tighter : left.cut.value ≤ right.cut.value :=
              cutLe_iff left right |>.mp (by
                simpa [Bound.cutLe] using comparison)
            simp only [Contains]
            constructor
            · intro upper
              exact ⟨upper, le_trans upper tighter⟩
            · exact fun both => both.1
          · have tighter : right.cut.value ≤ left.cut.value := by
              have notLe : ¬ left.cut.value ≤ right.cut.value := by
                intro le
                have raw := (cutLe_iff left right).mpr le
                exact comparison (by simpa [Bound.cutLe] using raw)
              exact le_of_not_ge notLe
            simp only [Contains]
            constructor
            · intro upper
              exact ⟨le_trans upper tighter, upper⟩
            · exact fun both => both.2

theorem sameCut_iff (left right : Bound) :
    left.sameCut right ↔ ∀ value, Contains left value ↔ Contains right value := by
  cases left with
  | all =>
      cases right with
      | all => simp [Bound.sameCut, Contains]
      | upper right =>
          simp only [Bound.sameCut, Bool.false_eq_true, false_iff]
          intro equivalent
          have impossible := (equivalent (right.cut.value + 1)).mp trivial
          simp only [Contains] at impossible
          linarith
  | upper left =>
      cases right with
      | all =>
          simp only [Bound.sameCut, Bool.false_eq_true, false_iff]
          intro equivalent
          have impossible := (equivalent (left.cut.value + 1)).mpr trivial
          simp only [Contains] at impossible
          linarith
      | upper right =>
          simp only [Bound.sameCut, Bool.and_eq_true, Contains]
          constructor
          · rintro ⟨forward, backward⟩ value
            have forwardValue : left.cut.value ≤ right.cut.value :=
              (cutLe_iff left right).mp (by
                simpa [Bound.cutLe] using forward)
            have backwardValue : right.cut.value ≤ left.cut.value :=
              (cutLe_iff right left).mp (by
                simpa [Bound.cutLe] using backward)
            exact ⟨fun bound => le_trans bound forwardValue,
              fun bound => le_trans bound backwardValue⟩
          · intro equivalent
            constructor
            · have raw := (cutLe_iff left right).mpr
                ((equivalent left.cut.value).mp le_rfl)
              simpa [Bound.cutLe] using raw
            · have raw := (cutLe_iff right left).mpr
                ((equivalent right.cut.value).mpr le_rfl)
              simpa [Bound.cutLe] using raw

def sourceModel : OperationSemantics.Model ℝ :=
  { operation := sourceOperation, relation := fun inputs _ => inputs = [] }

noncomputable def rowS (certificate : RowCertificate) : ℝ :=
  (certificate.capital.value + 1) *
      Real.exp (-(certificate.row : ℝ) / 2) +
    1.03883 * Real.exp (-(2 * certificate.row : ℝ) / 3) +
    certificate.c.value * Real.exp (-(3 * certificate.row : ℝ) / 4) +
    1.03883 * Real.exp (-(4 * certificate.row : ℝ) / 5)

noncomputable def rowValue (certificate : RowCertificate) (column : Nat) : ℝ :=
  (certificate.row : ℝ) ^ column * rowS certificate

noncomputable def rowValues (certificate : RowCertificate) : List ℝ :=
  [rowValue certificate 1, rowValue certificate 2, rowValue certificate 3,
    rowValue certificate 4, rowValue certificate 5]

noncomputable def ordinaryValues : List ℝ := ordinaryRows.flatMap rowValues

def batchModel : OperationSemantics.Model ℝ :=
  { operation := batchOperation, relation := fun inputs _ => inputs = ordinaryValues }

def operationModels : Array (OperationSemantics.Model ℝ) := #[sourceModel, batchModel]

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
            exact containsMeet previous proposed (valuation _) }
    else none

def laws : Laws semantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change Contains fact (valuation left) ↔ Contains fact (valuation right)
      rw [values] }

private theorem halfWindow :
    Real.exp (-(1 : ℝ) / 2) < 0.606530660 := by
  have remainder := Real.exp_bound
    (x := (-(1 : ℝ) / 2)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  linarith

private theorem twoThirdsWindow :
    Real.exp (-(2 : ℝ) / 3) < 0.513417120 := by
  have remainder := Real.exp_bound
    (x := (-(2 : ℝ) / 3)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  linarith

private theorem threeQuartersWindow :
    Real.exp (-(3 : ℝ) / 4) < 0.472366553 := by
  have remainder := Real.exp_bound
    (x := (-(3 : ℝ) / 4)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  linarith

private theorem fourFifthsWindow :
    Real.exp (-(4 : ℝ) / 5) < 0.449328965 := by
  have remainder := Real.exp_bound
    (x := (-(4 : ℝ) / 5)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  linarith

private theorem expTermsUpper (b : Nat) (positive : b ≠ 0) :
    Real.exp (-(b : ℝ) / 2) < (0.606530660 : ℝ) ^ b ∧
      Real.exp (-(2 * b : ℝ) / 3) < (0.513417120 : ℝ) ^ b ∧
      Real.exp (-(3 * b : ℝ) / 4) < (0.472366553 : ℝ) ^ b ∧
      Real.exp (-(4 * b : ℝ) / 5) < (0.449328965 : ℝ) ^ b := by
  have h1 := pow_lt_pow_left₀ halfWindow
    (Real.exp_pos (-(1 : ℝ) / 2)).le positive
  have h2 := pow_lt_pow_left₀ twoThirdsWindow
    (Real.exp_pos (-(2 : ℝ) / 3)).le positive
  have h3 := pow_lt_pow_left₀ threeQuartersWindow
    (Real.exp_pos (-(3 : ℝ) / 4)).le positive
  have h4 := pow_lt_pow_left₀ fourFifthsWindow
    (Real.exp_pos (-(4 : ℝ) / 5)).le positive
  rw [← Real.exp_nat_mul] at h1 h2 h3 h4
  constructor
  · rw [show -(b : ℝ) / 2 = (b : ℝ) * (-(1 : ℝ) / 2) by ring]
    exact h1
  constructor
  · rw [show -(2 * b : ℝ) / 3 = (b : ℝ) * (-(2 : ℝ) / 3) by
      ring]
    exact h2
  constructor
  · rw [show -(3 * b : ℝ) / 4 = (b : ℝ) * (-(3 : ℝ) / 4) by
      ring]
    exact h3
  · rw [show -(4 * b : ℝ) / 5 = (b : ℝ) * (-(4 : ℝ) / 5) by
      ring]
    exact h4

noncomputable def rationalS (certificate : RowCertificate) : ℝ :=
  (certificate.capital.value + 1) * 0.606530660 ^ certificate.row +
    1.03883 * 0.513417120 ^ certificate.row +
    certificate.c.value * 0.472366553 ^ certificate.row +
    1.03883 * 0.449328965 ^ certificate.row

def RowHolds (certificate : RowCertificate) : Prop :=
  rowValue certificate 1 ≤ certificate.cell1.value ∧
    rowValue certificate 2 ≤ certificate.cell2.value ∧
    rowValue certificate 3 ≤ certificate.cell3.value ∧
    rowValue certificate 4 ≤ certificate.cell4.value ∧
    rowValue certificate 5 ≤ certificate.cell5.value

private theorem rowBoundsOfChecked (certificate : RowCertificate)
    (rowPositive : certificate.row ≠ 0)
    (cNonnegative : 0 ≤ certificate.c.value)
    (capitalNonnegative : 0 ≤ certificate.capital.value)
    (cell1 : (certificate.row : ℝ) ^ 1 * rationalS certificate ≤
      certificate.cell1.value)
    (cell2 : (certificate.row : ℝ) ^ 2 * rationalS certificate ≤
      certificate.cell2.value)
    (cell3 : (certificate.row : ℝ) ^ 3 * rationalS certificate ≤
      certificate.cell3.value)
    (cell4 : (certificate.row : ℝ) ^ 4 * rationalS certificate ≤
      certificate.cell4.value)
    (cell5 : (certificate.row : ℝ) ^ 5 * rationalS certificate ≤
      certificate.cell5.value) : RowHolds certificate := by
  have terms := expTermsUpper certificate.row rowPositive
  have shared : rowS certificate ≤ rationalS certificate := by
    unfold rowS rationalS
    have capitalPlus : 0 ≤ certificate.capital.value + 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left terms.1.le capitalPlus,
      mul_le_mul_of_nonneg_left terms.2.1.le (by norm_num : (0 : ℝ) ≤ 1.03883),
      mul_le_mul_of_nonneg_left terms.2.2.1.le cNonnegative,
      mul_le_mul_of_nonneg_left terms.2.2.2.le (by norm_num : (0 : ℝ) ≤ 1.03883)]
  unfold RowHolds rowValue
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_left shared (by positivity)) cell1
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_left shared (by positivity)) cell2
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_left shared (by positivity)) cell3
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_left shared (by positivity)) cell4
  · exact le_trans (mul_le_mul_of_nonneg_left shared (by positivity)) cell5

/-- Every generated ordinary row certificate is numerically valid. -/
theorem ordinaryRowsBounds (certificate : RowCertificate)
    (member : certificate ∈ ordinaryRows) : RowHolds certificate := by
  simp only [ordinaryRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals apply rowBoundsOfChecked <;>
    norm_num [row, decimal, Decimal.value, rationalS]

theorem rowCellsBounds (certificate : RowCertificate) (bounds : RowHolds certificate) :
    List.Forall₂ (· ≤ Decimal.value ·.cut) (rowValues certificate)
      certificate.cells := by
  rcases bounds with ⟨h1, h2, h3, h4, h5⟩
  simp [rowValues, RowCertificate.cells, h1, h2, h3, h4, h5]

private theorem forall₂_append {relation : α → β → Prop}
    {left₁ left₂ : List α} {right₁ right₂ : List β}
    (first : List.Forall₂ relation left₁ right₁)
    (second : List.Forall₂ relation left₂ right₂) :
    List.Forall₂ relation (left₁ ++ left₂) (right₁ ++ right₂) := by
  induction first with
  | nil => exact second
  | cons head tail induction => exact .cons head induction

theorem rowsCellsBounds (rows : List RowCertificate)
    (bounds : ∀ certificate ∈ rows, RowHolds certificate) :
    List.Forall₂ (· ≤ Decimal.value ·.cut) (rows.flatMap rowValues)
      (rows.flatMap RowCertificate.cells) := by
  induction rows with
  | nil => simp
  | cons head tail induction =>
      rw [List.flatMap_cons, List.flatMap_cons]
      exact forall₂_append (rowCellsBounds head (bounds head (by simp)))
        (induction (by
          intro certificate member
          exact bounds certificate (by simp [member])))

theorem ordinaryCellsBounds :
    List.Forall₂ (· ≤ Decimal.value ·.cut) ordinaryValues ordinaryCells := by
  exact rowsCellsBounds ordinaryRows ordinaryRowsBounds

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

private theorem cellEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (anchor : NodeId) (instruction : Node) (target : NodeId)
    (cell : CellCertificate) (index : Nat)
    (found : graph.node? anchor = some instruction)
    (operation : instruction.op = { index := 1 })
    (targetFound : instruction.args[index]? = some target)
    (cellFound : ordinaryCells[index]? = some cell)
    (_noAssumptions : assumptions = []) :
    semantics.Entails graph assumptions { node := target, fact := .upper cell } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains (.upper cell) (valuation target)
  intro valuation models _
  obtain ⟨meaning, meaningAt, related⟩ := models.2 anchor instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have values : instruction.args.map valuation = ordinaryValues := by
    change instruction.args.map valuation = ordinaryValues at related
    exact related
  obtain ⟨input, inputFound, inputBound⟩ :=
    forall₂_right_get? ordinaryCellsBounds index cell cellFound
  have mappedTarget : (instruction.args.map valuation)[index]? =
      some (valuation target) := by
    simp [targetFound]
  have targetValue : ordinaryValues[index]? = some (valuation target) := by
    rw [← values]
    exact mappedTarget
  have targetInput : valuation target = input := by
    exact Option.some.inj (targetValue.symm.trans inputFound)
  change valuation target ≤ cell.cut.value
  simpa [targetInput] using inputBound

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) : fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def batchFactSchema : PackedFactSchema semantics where
  rule := batchRuleKey
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
                match cellFound : ordinaryCells[index]? with
                | some expected =>
                    if cellExact : cell = expected then
                      if targetFound : instruction.args[index]? =
                          some context.proposed.node then
                        some
                          { proof := by
                              subst expected
                              have proposedEq : context.proposed =
                                  { node := context.proposed.node,
                                    fact := .upper cell } :=
                                factWith context.proposed proposedFact
                              rw [proposedEq]
                              exact cellEntails context.program context.assumptions
                                action.node instruction context.proposed.node cell index
                                found operation targetFound cellFound noAssumptions }
                      else none
                    else none
                | none => none
            | .all => none
          else
            none
        else
          none
    | none => none

def stableLaw : StableLaw semantics :=
  OperationSemantics.stableLaw operationModels Contains

def sourceEmit : EmitPackage Lean.Name := { schemas := [] }
def batchEmit : EmitPackage Lean.Name :=
  { schemas := [{ key := batchFactSchema.key, handle := ``batchFactSchema }] }

def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }, emit := sourceEmit }

def batchProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[batchFactSchema] }, emit := batchEmit }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, batchProof]

structure SourceRow where
  b : ℝ
  cb1 : ℝ
  cb2 : ℝ
  cb3 : ℝ
  cb4 : ℝ
  cb5 : ℝ
  c : ℝ
  capital : ℝ
  m : ℝ

noncomputable def source (b cb1 cb2 cb3 cb4 cb5 c capital m : ℝ) : SourceRow :=
  { b, cb1, cb2, cb3, cb4, cb5, c, capital, m }

noncomputable def RowCertificate.sourceRow (certificate : RowCertificate) : SourceRow :=
  source certificate.row certificate.cell1.value certificate.cell2.value
    certificate.cell3.value certificate.cell4.value certificate.cell5.value
    certificate.c.value certificate.capital.value
    (certificate.mMantissa * (10 : ℝ) ^ certificate.mExponent)

/-- Exact scientific-decimal correspondence with every non-logarithmic tuple
except row 25, which remains authenticated by the original fixture. -/
theorem ordinaryCertificatesMatchSource :
    ordinaryRows.map RowCertificate.sourceRow = [
      source 20 1.68440e-3 3.36880e-2 6.73750e-1 1.34750e1 2.69500e2 0.8 0.81 5e10,
      source 21 1.06840e-3 2.24350e-2 4.71140e-1 9.89390e0 2.07780e2 0.8 0.81 5e10,
      source 22 6.76540e-4 1.48840e-2 3.27450e-1 7.20380e0 1.58490e2 0.8 0.81 5e10,
      source 23 4.27800e-4 9.83920e-3 2.26310e-1 5.20500e0 1.19720e2 0.8 0.81 5e10,
      source 24 2.70120e-4 6.48290e-3 1.55590e-1 3.73410e0 8.96190e1 0.8 0.81 5e10,
      source 26 1.10220e-4 2.86560e-3 7.45050e-2 1.93720e0 5.03650e1 0.88 0.86 32e12,
      source 27 6.93270e-5 1.87190e-3 5.05400e-2 1.36460e0 3.68430e1 0.88 0.86 32e12,
      source 28 4.35580e-5 1.21970e-3 3.41500e-2 9.56180e-1 2.67730e1 0.88 0.86 32e12,
      source 29 2.73380e-5 7.92780e-4 2.29910e-2 6.66730e-1 1.93360e1 0.88 0.86 32e12,
      source 30 1.71400e-5 5.14180e-4 1.54260e-2 4.62760e-1 1.38830e1 0.88 0.86 32e12,
      source 31 1.07350e-5 3.32790e-4 1.034630e-2 3.217360e-1 1.000500e1 0.88 0.86 32e12,
      source 32 7.005640e-6 2.241810e-4 7.173770e-3 2.295610e-1 7.345940e0 0.94 0.94 1e19,
      source 33 4.38000e-6 1.44540e-4 4.76990e-3 1.57410e-1 5.19440e0 0.94 0.94 1e19,
      source 34 2.73610e-6 9.30270e-5 3.16300e-3 1.07540e-1 3.65640e0 0.94 0.94 1e19,
      source 35 1.70780e-6 5.97730e-5 2.09210e-3 7.32220e-2 2.56280e0 0.94 0.94 1e19,
      source 36 1.06520e-6 3.83460e-5 1.38050e-3 4.96960e-2 1.78910e0 0.94 0.94 1e19,
      source 37 6.63850e-7 2.45630e-5 9.08810e-4 3.36260e-2 1.24420e0 0.94 0.94 1e19,
      source 38 4.13450e-7 1.57120e-5 5.97020e-4 2.26870e-2 8.62100e-1 0.94 0.94 1e19,
      source 39 2.57330e-7 1.00360e-5 3.91400e-4 1.52650e-2 5.95320e-1 0.94 0.94 1e19,
      source 40 1.60060e-7 6.40240e-6 2.56100e-4 1.02440e-2 4.09750e-1 0.94 0.94 1e19,
      source 41 9.94970e-8 4.07940e-6 1.67260e-4 6.85740e-3 2.81160e-1 0.94 0.94 1e19,
      source 42 6.18140e-8 2.59620e-6 1.09040e-4 4.57970e-3 1.92350e-1 0.94 0.94 1e19,
      source 43 3.83820e-8 1.65050e-6 7.09680e-5 3.05170e-3 1.31220e-1 0.94 0.94 1e19] := by
  norm_num [ordinaryRows, RowCertificate.sourceRow, source, row, decimal,
    Decimal.value, OfScientific.ofScientific]

set_option maxRecDepth 10000 in
/-- Exact structural sizes of the generated ordinary-row payload. -/
theorem ordinaryCertificateCount :
    ordinaryRows.length = 23 ∧ ordinaryCells.length = 115 ∧ batchBody.length = 391 := by
  decide

end Hex.Interval.Experiment.PntTable12Ordinary
