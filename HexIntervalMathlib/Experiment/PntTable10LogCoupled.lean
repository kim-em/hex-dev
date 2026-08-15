/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import HexIntervalMathlib.Experiment.PntTable10Shard
public import HexInterval.Experiment.PntTable10LogCoupled

@[expose] public section

/-!
# Ordinary-kernel semantics for the Table 10 logarithmic transition

The runtime certificate's shared rational endpoint data is connected here to
`19 * Real.log 10`.  A kernel-checked logarithm window establishes the row
ordering and the polynomial-factor bound, while exact real-power identities
establish both exponential-tail assumptions.  Convexity then covers both
complete source intervals.
-/

namespace Hex.Interval.Experiment.PntTable10LogCoupled

open Real Set Finset
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics
open PntTable10Shard

theorem decimalPowValue (value : Decimal) (power : Nat) :
    (decimalPow value power).value = value.value ^ power := by
  unfold decimalPow Decimal.value decimal
  push_cast
  rw [pow_mul, div_pow]

private theorem logFiveWindow :
    (1.6094379124 : ℝ) < Real.log 5 ∧ Real.log 5 < (1.609437913 : ℝ) := by
  have habs : |(4 / 5 : ℝ)| = 4 / 5 := by norm_num
  have remainder := Real.abs_log_sub_add_sum_range_le
    (x := (4 / 5 : ℝ)) (by norm_num) 150
  rw [habs, show (1 - 4 / 5 : ℝ) = 1 / 5 by norm_num,
      show (1 / 5 : ℝ) = (5 : ℝ)⁻¹ by norm_num,
      Real.log_inv, ← sub_eq_add_neg, abs_sub_comm] at remainder
  rw [abs_le] at remainder
  constructor <;> norm_num [sum_range_succ] at remainder ⊢ <;> linarith

theorem logTenWindow :
    (2.3025850924 : ℝ) < Real.log 10 ∧ Real.log 10 < (2.302585094 : ℝ) := by
  have identity : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [identity]
  constructor
  · nlinarith [Real.log_two_gt_d9, logFiveWindow.1]
  · nlinarith [Real.log_two_lt_d9, logFiveWindow.2]

theorem rowChronology :
    (43 : ℝ) ≤ 19 * Real.log 10 ∧ 19 * Real.log 10 ≤ 44 := by
  constructor <;> nlinarith [logTenWindow.1, logTenWindow.2]

theorem logPointUpper : 19 * Real.log 10 ≤ (43.75 : ℝ) := by
  nlinarith [logTenWindow.2]

private theorem rpowLeOfPowLe {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    {p q : Nat} (hq : q ≠ 0) (bound : a ^ p ≤ c ^ q) :
    a ^ (p / (q : ℝ)) ≤ c := by
  have powerIdentity : (a ^ (p / (q : ℝ))) ^ q = a ^ p := by
    have castNonzero : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    calc
      (a ^ (p / (q : ℝ))) ^ q = a ^ ((p / (q : ℝ)) * q) := by
        symm
        exact Real.rpow_mul_natCast ha (p / (q : ℝ)) q
      _ = a ^ (p : ℝ) := by field_simp [castNonzero]
      _ = a ^ p := by simp [Real.rpow_natCast]
  have powered : (a ^ (p / (q : ℝ))) ^ q ≤ c ^ q := by
    simpa [powerIdentity] using bound
  exact (pow_le_pow_iff_left₀ (by positivity) hc hq).1 powered

theorem halfTailUpper :
    Real.exp (-(1 / 2 * (19 * Real.log 10))) ≤ (3.17e-10 : ℝ) := by
  have identity : Real.exp (-(1 / 2 * (19 * Real.log 10))) =
      (1 / 10 : ℝ) ^ ((19 : ℝ) / 2) := by
    have exponent : -(1 / 2 * (19 * Real.log 10)) =
        Real.log 10 * (-(19 : ℝ) / 2) := by ring
    calc
      _ = Real.exp (Real.log 10 * (-(19 : ℝ) / 2)) := by rw [exponent]
      _ = Real.exp (Real.log 10) ^ (-(19 : ℝ) / 2) := by
        simpa using (Real.exp_mul (Real.log 10) (-(19 : ℝ) / 2))
      _ = Real.exp (Real.log 10) ^ (-((19 : ℝ) / 2)) := by simp [neg_div]
      _ = (10 : ℝ) ^ (-((19 : ℝ) / 2)) := by
        simp [Real.exp_log (by norm_num : (0 : ℝ) < 10)]
      _ = (1 / 10 : ℝ) ^ ((19 : ℝ) / 2) := by
        simpa [one_div] using (rpow_neg_eq_inv_rpow (10 : ℝ) ((19 : ℝ) / 2))
  rw [identity]
  refine rpowLeOfPowLe (a := 1 / 10) (c := 3.17e-10) (by norm_num) (by norm_num)
    (p := 19) (q := 2) (by norm_num) ?_
  norm_num

theorem twoThirdTailUpper :
    Real.exp (-(2 / 3 * (19 * Real.log 10))) ≤ (2.16e-13 : ℝ) := by
  have identity : Real.exp (-(2 / 3 * (19 * Real.log 10))) =
      (1 / 10 : ℝ) ^ ((38 : ℝ) / 3) := by
    have exponent : -(2 / 3 * (19 * Real.log 10)) =
        Real.log 10 * (-(38 : ℝ) / 3) := by ring
    calc
      _ = Real.exp (Real.log 10 * (-(38 : ℝ) / 3)) := by rw [exponent]
      _ = Real.exp (Real.log 10) ^ (-(38 : ℝ) / 3) := by
        simpa using (Real.exp_mul (Real.log 10) (-(38 : ℝ) / 3))
      _ = Real.exp (Real.log 10) ^ (-((38 : ℝ) / 3)) := by simp [neg_div]
      _ = (10 : ℝ) ^ (-((38 : ℝ) / 3)) := by
        simp [Real.exp_log (by norm_num : (0 : ℝ) < 10)]
      _ = (1 / 10 : ℝ) ^ ((38 : ℝ) / 3) := by
        simpa [one_div] using (rpow_neg_eq_inv_rpow (10 : ℝ) ((38 : ℝ) / 3))
  rw [identity]
  refine rpowLeOfPowLe (a := 1 / 10) (c := 2.16e-13) (by norm_num) (by norm_num)
    (p := 38) (q := 3) (by norm_num) ?_
  norm_num

noncomputable def lowerPoint (row : RowCertificate) : ℝ :=
  if row.rowCode = 43 then 43 else 19 * Real.log 10

noncomputable def upperPoint (row : RowCertificate) : ℝ :=
  if row.rowCode = 43 then 19 * Real.log 10 else 44

noncomputable def majorant (row : RowCertificate) (column : Nat) (y : ℝ) : ℝ :=
  coefficientMajorant row.a1.value row.a2.value row.epsilon.value column y

noncomputable def endpointValue (row : RowCertificate) (cell : Cell) : ℝ :=
  max (majorant row cell.coordinate.column (lowerPoint row))
    (majorant row cell.coordinate.column (upperPoint row))

def rowCells : List (RowCertificate × Cell) :=
  (rows certificate).flatMap fun row => row.cells.map fun cell => (row, cell)

noncomputable def endpointValues : List ℝ :=
  rowCells.map fun pair => endpointValue pair.1 pair.2

private theorem integerApprox (row : RowCertificate) (cell : Cell) (point : Nat)
    (positive : point ≠ 0) :
    majorant row cell.coordinate.column point ≤
      (integerEndpoint certificate row cell point).value := by
  have windows := expTermsUpper point positive
  have halfValue : certificate.halfBase.value = (0.606530660 : ℝ) := by
    norm_num [certificate, Decimal.value, decimal]
  have twoThirdValue : certificate.twoThirdBase.value = (0.513417120 : ℝ) := by
    norm_num [certificate, Decimal.value, decimal]
  unfold majorant coefficientMajorant integerEndpoint
  simp only [decimalMulValue, decimalAddValue]
  rw [decimalPowNatValue, decimalPowValue, decimalPowValue]
  calc
    _ = (point : ℝ) ^ cell.coordinate.column *
        (row.a1.value * Real.exp (-(point : ℝ) / 2) +
          (row.a2.value * Real.exp (-(2 * point : ℝ) / 3) + row.epsilon.value)) := by
        ring_nf
    _ ≤ (point : ℝ) ^ cell.coordinate.column *
        (row.a1.value * (0.606530660 : ℝ) ^ point +
          (row.a2.value * (0.513417120 : ℝ) ^ point + row.epsilon.value)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left windows.1.le (by
            unfold Decimal.value
            positivity)
        · exact add_le_add (mul_le_mul_of_nonneg_left windows.2.le (by
            unfold Decimal.value
            positivity)) le_rfl
    _ = _ := by rw [halfValue, twoThirdValue]

private theorem logApprox (row : RowCertificate) (cell : Cell) :
    majorant row cell.coordinate.column (19 * Real.log 10) ≤
      (logEndpoint certificate row cell).value := by
  have pointNonneg : (0 : ℝ) ≤ 19 * Real.log 10 := by linarith [rowChronology.1]
  have powerBound : (19 * Real.log 10) ^ cell.coordinate.column ≤
      (43.75 : ℝ) ^ cell.coordinate.column := by
    exact pow_le_pow_left₀ pointNonneg logPointUpper cell.coordinate.column
  have logValue : certificate.logUpper.value = (43.75 : ℝ) := by
    norm_num [certificate, Decimal.value, decimal]
  have halfValue : certificate.halfTail.value = (3.17e-10 : ℝ) := by
    norm_num [certificate, Decimal.value, decimal]
  have twoThirdValue : certificate.twoThirdTail.value = (2.16e-13 : ℝ) := by
    norm_num [certificate, Decimal.value, decimal]
  have halfBound : Real.exp (-(19 * Real.log 10 / 2)) ≤ (3.17e-10 : ℝ) := by
    convert halfTailUpper using 1
    ring_nf
  have twoThirdBound : Real.exp (-(2 * (19 * Real.log 10) / 3)) ≤
      (2.16e-13 : ℝ) := by
    convert twoThirdTailUpper using 1
    ring_nf
  have hA1 : 0 ≤ row.a1.value := by unfold Decimal.value; positivity
  have hA2 : 0 ≤ row.a2.value := by unfold Decimal.value; positivity
  have hE : 0 ≤ row.epsilon.value := by unfold Decimal.value; positivity
  unfold majorant coefficientMajorant logEndpoint
  simp only [decimalMulValue, decimalAddValue]
  rw [decimalPowValue, logValue, halfValue, twoThirdValue]
  calc
    _ = (19 * Real.log 10) ^ cell.coordinate.column *
        (row.a1.value * Real.exp (-(19 * Real.log 10 / 2)) +
          (row.a2.value * Real.exp (-(2 * (19 * Real.log 10) / 3)) +
            row.epsilon.value)) := by ring
    _ ≤ (43.75 : ℝ) ^ cell.coordinate.column *
        (row.a1.value * (3.17e-10 : ℝ) +
          (row.a2.value * (2.16e-13 : ℝ) + row.epsilon.value)) := by
      apply mul_le_mul powerBound
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left halfBound hA1
        · exact add_le_add (mul_le_mul_of_nonneg_left twoThirdBound hA2) le_rfl
      · exact add_nonneg (mul_nonneg hA1 (Real.exp_pos _).le)
          (add_nonneg (mul_nonneg hA2 (Real.exp_pos _).le) hE)
      · positivity

private theorem pairApprox (row : RowCertificate) (cell : Cell)
    (rowMember : row ∈ rows certificate) :
    majorant row cell.coordinate.column (lowerPoint row) ≤
        (leftEndpoint certificate row cell).value ∧
      majorant row cell.coordinate.column (upperPoint row) ≤
        (rightEndpoint certificate row cell).value := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at rowMember
  rcases rowMember with rfl | rfl
  · exact ⟨by simpa [certificate, lowerPoint, leftEndpoint, row43, rowCertificate] using
        integerApprox row43 cell 43 (by norm_num),
      by simpa [certificate, upperPoint, rightEndpoint, row43, rowCertificate] using
        logApprox row43 cell⟩
  · exact ⟨by simpa [certificate, lowerPoint, leftEndpoint, rowLog, rowCertificate,
        logRowCode] using
        logApprox rowLog cell,
      by simpa [certificate, upperPoint, rightEndpoint, rowLog, rowCertificate,
        logRowCode] using
        integerApprox rowLog cell 44 (by norm_num)⟩

private theorem rowBounds (row : RowCertificate) (member : row ∈ rows certificate) :
    (20 : ℝ) ≤ lowerPoint row ∧ lowerPoint row ≤ upperPoint row := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simpa [certificate, lowerPoint, upperPoint, row43, rowCertificate] using
      (show (20 : ℝ) ≤ 43 ∧ (43 : ℝ) ≤ 19 * Real.log 10 by
        exact ⟨by norm_num, rowChronology.1⟩)
  · simpa [certificate, lowerPoint, upperPoint, rowLog, rowCertificate, logRowCode] using
      (show (20 : ℝ) ≤ 19 * Real.log 10 ∧ 19 * Real.log 10 ≤ 44 by
        exact ⟨by linarith [rowChronology.1], rowChronology.2⟩)

private theorem cellOfCheck (row : RowCertificate) (cell : Cell)
    (rowMember : row ∈ rows certificate) (checked : checkCell certificate row cell = true) :
    ∀ y ∈ Icc (lowerPoint row) (upperPoint row),
      majorant row cell.coordinate.column y ≤ cell.target.value := by
  rw [checkCell] at checked
  simp only [Bool.and_eq_true] at checked
  have column : 1 ≤ cell.coordinate.column ∧ cell.coordinate.column ≤ 5 :=
    of_decide_eq_true checked.1.1.1.2
  have approximations := pairApprox row cell rowMember
  have endpointBound : endpointValue row cell ≤ cell.target.value := by
    rw [endpointValue, max_le_iff]
    exact ⟨approximations.1.trans ((decimalLe_iff _ _).mp checked.1.2),
      approximations.2.trans ((decimalLe_iff _ _).mp checked.2)⟩
  intro y hy
  have bounds := rowBounds row rowMember
  have convex : ConvexOn ℝ (Icc (lowerPoint row) (upperPoint row))
      (majorant row cell.coordinate.column) := by
    obtain ⟨columnLower, columnUpper⟩ := column
    have hA1 : 0 ≤ row.a1.value := by unfold Decimal.value; positivity
    have hA2 : 0 ≤ row.a2.value := by unfold Decimal.value; positivity
    have hE : 0 ≤ row.epsilon.value := by unfold Decimal.value; positivity
    interval_cases cell.coordinate.column
    · exact coefficientMajorantConvex1 bounds.1 hA1 hA2
    · exact coefficientMajorantConvexSucc bounds.1 0 (by norm_num) hA1 hA2 hE
    · exact coefficientMajorantConvexSucc bounds.1 1 (by norm_num) hA1 hA2 hE
    · exact coefficientMajorantConvexSucc bounds.1 2 (by norm_num) hA1 hA2 hE
    · exact coefficientMajorantConvexSucc bounds.1 3 (by norm_num) hA1 hA2 hE
  exact (convex.le_max_of_mem_Icc ⟨le_rfl, bounds.2⟩ ⟨bounds.2, le_rfl⟩ hy).trans
    endpointBound

private theorem pairParts (row : RowCertificate) (cell : Cell)
    (member : (row, cell) ∈ rowCells) :
    row ∈ rows certificate ∧ cell ∈ row.cells := by
  rw [rowCells, List.mem_flatMap] at member
  obtain ⟨sourceRow, rowMember, pairMember⟩ := member
  rw [List.mem_map] at pairMember
  obtain ⟨sourceCell, cellMember, pairEq⟩ := pairMember
  have rowEq : sourceRow = row := congrArg Prod.fst pairEq
  have cellEq : sourceCell = cell := congrArg Prod.snd pairEq
  subst sourceRow
  subst sourceCell
  exact ⟨rowMember, cellMember⟩

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
private theorem sourceChecked (row : RowCertificate) (cell : Cell)
    (rowMember : row ∈ rows certificate) (cellMember : cell ∈ row.cells) :
    checkCell certificate row cell = true := by
  have valid : (rows certificate).all
      (fun sourceRow => sourceRow.cells.all (checkCell certificate sourceRow)) = true := by decide
  rw [List.all_eq_true] at valid
  have rowValid := valid row rowMember
  rw [List.all_eq_true] at rowValid
  exact rowValid cell cellMember

/-- Every coordinate in the authenticated coupled batch has its corrected
source bound on its complete real interval. -/
theorem rowCell (row : RowCertificate) (cell : Cell)
    (member : (row, cell) ∈ rowCells) :
    ∀ y ∈ Icc (lowerPoint row) (upperPoint row),
      majorant row cell.coordinate.column y ≤ cell.target.value := by
  obtain ⟨rowMember, cellMember⟩ := pairParts row cell member
  exact cellOfCheck row cell rowMember (sourceChecked row cell rowMember cellMember)

abbrev SourceTuple := ℝ × ℝ × ℝ × ℝ × ℝ × ℝ

noncomputable def sourceTuple (row : RowCertificate) : SourceTuple :=
  (lowerPoint row, row.cell1.listed.value, row.cell2.listed.value,
    row.cell3.listed.value, row.cell4.listed.value, row.cell5.listed.value)

/-- The exact consecutive tuples at pinned `BKLNW_tables.lean:815–816`. -/
noncomputable def sourceTable : List SourceTuple :=
  (rows certificate).map sourceTuple

private theorem rowOfAbscissa (observed row : RowCertificate)
    (observedMember : observed ∈ rows certificate) (rowMember : row ∈ rows certificate)
    (equal : lowerPoint observed = lowerPoint row) : observed = row := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at observedMember rowMember
  rcases observedMember with rfl | rfl <;> rcases rowMember with rfl | rfl
  · rfl
  · exfalso
    simp [certificate, lowerPoint, row43, rowLog, rowCertificate, logRowCode] at equal
    nlinarith [logTenWindow.1]
  · exfalso
    simp [certificate, lowerPoint, row43, rowLog, rowCertificate, logRowCode] at equal
    nlinarith [logTenWindow.1]
  · rfl

private theorem sourceValues (row : RowCertificate) (rowMember : row ∈ rows certificate)
    (B : Nat → ℝ)
    (member : (lowerPoint row, B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    B 1 = row.cell1.listed.value ∧ B 2 = row.cell2.listed.value ∧
      B 3 = row.cell3.listed.value ∧ B 4 = row.cell4.listed.value ∧
      B 5 = row.cell5.listed.value := by
  rw [sourceTable, List.mem_map] at member
  obtain ⟨observed, observedMember, tupleEq⟩ := member
  have abscissaEq : lowerPoint observed = lowerPoint row := by
    exact congrArg Prod.fst tupleEq
  have observedEq := rowOfAbscissa observed row observedMember rowMember abscissaEq
  subst observed
  have h1 := congrArg (fun tuple : SourceTuple => tuple.2.1) tupleEq
  have h2 := congrArg (fun tuple : SourceTuple => tuple.2.2.1) tupleEq
  have h3 := congrArg (fun tuple : SourceTuple => tuple.2.2.2.1) tupleEq
  have h4 := congrArg (fun tuple : SourceTuple => tuple.2.2.2.2.1) tupleEq
  have h5 := congrArg (fun tuple : SourceTuple => tuple.2.2.2.2.2) tupleEq
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm⟩

private theorem cellPair (row : RowCertificate) (rowMember : row ∈ rows certificate)
    (cell : Cell) (cellMember : cell ∈ row.cells) : (row, cell) ∈ rowCells := by
  rw [rowCells, List.mem_flatMap]
  exact ⟨row, rowMember, by simpa using cellMember⟩

private structure SourceShape (row : RowCertificate) : Prop where
  cell1 : row.cell1.coordinate.column = 1 ∧
    row.cell1.target = corrected row.cell1.listed
  cell2 : row.cell2.coordinate.column = 2 ∧
    row.cell2.target = corrected row.cell2.listed
  cell3 : row.cell3.coordinate.column = 3 ∧
    row.cell3.target = corrected row.cell3.listed
  cell4 : row.cell4.coordinate.column = 4 ∧
    row.cell4.target = corrected row.cell4.listed
  cell5 : row.cell5.coordinate.column = 5 ∧
    row.cell5.target = corrected row.cell5.listed

private theorem sourceShape (row : RowCertificate) (member : row ∈ rows certificate) :
    SourceShape row := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Source-dispatch-shaped replacement for all ten remaining Table 10 numeric
premises. PNT+ may locally rewrite its `B_8_exact` endpoint reduction to this
coefficient majorant. -/
theorem rowOfMem (row : RowCertificate) (rowMember : row ∈ rows certificate)
    (B : Nat → ℝ)
    (member : (lowerPoint row, B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    ∀ k ∈ Finset.Icc 1 5, ∀ y ∈ Set.Icc (lowerPoint row) (upperPoint row),
      majorant row k y ≤ B k * margin.value := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sourceValues row rowMember B member
  have shape := sourceShape row rowMember
  intro k hk
  simp only [Finset.mem_Icc] at hk
  obtain ⟨lower, upper⟩ := hk
  interval_cases k
  · simpa only [shape.cell1.1, shape.cell1.2, corrected, decimalMulValue, h1]
      using rowCell row row.cell1
        (cellPair row rowMember row.cell1 (by simp [RowCertificate.cells]))
  · simpa only [shape.cell2.1, shape.cell2.2, corrected, decimalMulValue, h2]
      using rowCell row row.cell2
        (cellPair row rowMember row.cell2 (by simp [RowCertificate.cells]))
  · simpa only [shape.cell3.1, shape.cell3.2, corrected, decimalMulValue, h3]
      using rowCell row row.cell3
        (cellPair row rowMember row.cell3 (by simp [RowCertificate.cells]))
  · simpa only [shape.cell4.1, shape.cell4.2, corrected, decimalMulValue, h4]
      using rowCell row row.cell4
        (cellPair row rowMember row.cell4 (by simp [RowCertificate.cells]))
  · simpa only [shape.cell5.1, shape.cell5.2, corrected, decimalMulValue, h5]
      using rowCell row row.cell5
        (cellPair row rowMember row.cell5 (by simp [RowCertificate.cells]))

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

private theorem endpointBound (row : RowCertificate) (cell : Cell)
    (member : (row, cell) ∈ rowCells) :
    endpointValue row cell ≤ cell.target.value := by
  rw [endpointValue, max_le_iff]
  exact ⟨rowCell row cell member (lowerPoint row)
      ⟨le_rfl, (rowBounds row (pairParts row cell member).1).2⟩,
    rowCell row cell member (upperPoint row)
      ⟨(rowBounds row (pairParts row cell member).1).2, le_rfl⟩⟩

private theorem mappedBounds (pairs : List (RowCertificate × Cell))
    (bounded : ∀ pair ∈ pairs, endpointValue pair.1 pair.2 ≤ pair.2.target.value) :
    List.Forall₂ (fun value cell => value ≤ cell.target.value)
      (pairs.map fun pair => endpointValue pair.1 pair.2) (pairs.map Prod.snd) := by
  induction pairs with
  | nil => exact .nil
  | cons pair remaining induction =>
      exact .cons (bounded pair (by simp))
        (induction fun current member => bounded current (by simp [member]))

theorem endpointValuesBound :
    List.Forall₂ (fun value cell => value ≤ cell.target.value)
      endpointValues (cells certificate) := by
  have cellsEq : cells certificate = rowCells.map Prod.snd := by
    simp [cells, rowCells, rows, RowCertificate.cells]
  rw [cellsEq]
  exact mappedBounds rowCells fun pair member => endpointBound pair.1 pair.2 member

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
    (cellFound : (cells certificate)[index]? = some cell)
    (_noAssumptions : assumptions = []) :
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
                match cellFound : (cells certificate)[index]? with
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

end Hex.Interval.Experiment.PntTable10LogCoupled
