/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntTable12Log
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics
public import HexIntervalMathlib.Experiment.PntTable12
public import HexIntervalMathlib.Experiment.PntTable12Ordinary

@[expose] public section

namespace Hex.Interval.Experiment.PntTable12Log

open Finset
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics
open PntTable12Ordinary

noncomputable def decimalValue (value : Decimal) : ℝ :=
  value.mantissa / (10 : ℝ) ^ value.scale

def lowerContains : Option Decimal → ℝ → Prop
  | none, _ => True
  | some lower, value => decimalValue lower ≤ value

def upperContains : Option Decimal → ℝ → Prop
  | none, _ => True
  | some upper, value => value ≤ decimalValue upper

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .range range, value => lowerContains range.lower value ∧ upperContains range.upper value
  | .empty, _ => False

theorem decimalLe_iff (left right : Decimal) :
    decimalLe left right ↔ decimalValue left ≤ decimalValue right := by
  simp only [decimalLe, decide_eq_true_eq]
  unfold decimalValue
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ left.scale)
    (by positivity : (0 : ℝ) < 10 ^ right.scale)]
  norm_cast

theorem lowerMaxContains (left right : Option Decimal) (value : ℝ) :
    lowerContains (Range.lowerMax left right) value ↔
      lowerContains left value ∧ lowerContains right value := by
  cases left with
  | none => simp [Range.lowerMax, lowerContains]
  | some left =>
      cases right with
      | none => simp [Range.lowerMax, lowerContains]
      | some right =>
          simp only [Range.lowerMax, decimalMax]
          split <;> rename_i comparison
          · have order := decimalLe_iff left right |>.mp (by simpa using comparison)
            simp only [lowerContains]
            constructor
            · exact fun upper => ⟨le_trans order upper, upper⟩
            · exact fun both => both.2
          · have order : decimalValue right ≤ decimalValue left := by
              apply le_of_not_ge
              intro contrary
              exact comparison (by simpa using (decimalLe_iff left right).mpr contrary)
            simp only [lowerContains]
            constructor
            · exact fun upper => ⟨upper, le_trans order upper⟩
            · exact fun both => both.1

theorem upperMinContains (left right : Option Decimal) (value : ℝ) :
    upperContains (Range.upperMin left right) value ↔
      upperContains left value ∧ upperContains right value := by
  cases left with
  | none => simp [Range.upperMin, upperContains]
  | some left =>
      cases right with
      | none => simp [Range.upperMin, upperContains]
      | some right =>
          simp only [Range.upperMin, decimalMin]
          split <;> rename_i comparison
          · have order := decimalLe_iff left right |>.mp (by simpa using comparison)
            simp only [upperContains]
            constructor
            · exact fun lower => ⟨lower, le_trans lower order⟩
            · exact fun both => both.1
          · have order : decimalValue right ≤ decimalValue left := by
              apply le_of_not_ge
              intro contrary
              exact comparison (by simpa using (decimalLe_iff left right).mpr contrary)
            simp only [upperContains]
            constructor
            · exact fun lower => ⟨le_trans lower order, lower⟩
            · exact fun both => both.2

theorem containsMeet (left right : Bound) (value : ℝ) :
    Contains (left.meet right) value ↔ Contains left value ∧ Contains right value := by
  cases left with
  | all => cases right <;> simp [Bound.meet, Contains]
  | empty => cases right <;> simp [Bound.meet, Contains]
  | range left =>
      cases right with
      | all => simp [Bound.meet, Contains]
      | empty => simp [Bound.meet, Contains]
      | range right =>
          simp only [Bound.meet, Contains, Range.intersect]
          rw [lowerMaxContains, upperMinContains]
          aesop

private theorem logFiveWindow :
    (1.6094379124 : ℝ) < Real.log 5 ∧ Real.log 5 < 1.609437913 := by
  have habs : |(4 : ℝ) / 5| = (4 : ℝ) / 5 := by norm_num
  have remainder := Real.abs_log_sub_add_sum_range_le
    (x := (4 : ℝ) / 5) (by norm_num) 150
  rw [habs, show (1 : ℝ) - 4 / 5 = 1 / 5 by norm_num,
    show (1 : ℝ) / 5 = (5 : ℝ)⁻¹ by norm_num,
    Real.log_inv, ← sub_eq_add_neg, abs_sub_comm] at remainder
  rw [abs_le] at remainder
  constructor <;> norm_num [sum_range_succ] at remainder ⊢ <;> linarith

private theorem logFiveE10Window :
    (24.6352888 : ℝ) ≤ Real.log 5e10 ∧ Real.log 5e10 ≤ 24.6352889 := by
  have identity : Real.log (5e10 : ℝ) =
      10 * Real.log 2 + 11 * Real.log 5 := by
    rw [show (5e10 : ℝ) = 2 ^ 10 * 5 ^ 11 by norm_num,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
  rw [identity]
  constructor
  · nlinarith [Real.log_two_gt_d9, logFiveWindow.1]
  · nlinarith [Real.log_two_lt_d9, logFiveWindow.2]

private theorem logThirtyTwoE12Window :
    (31.0967570 : ℝ) ≤ Real.log (32e12) ∧
      Real.log (32e12) ≤ 31.0967571 := by
  have identity : Real.log (32e12 : ℝ) =
      17 * Real.log 2 + 12 * Real.log 5 := by
    rw [show (32e12 : ℝ) = 2 ^ 17 * 5 ^ 12 by norm_num,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
  rw [identity]
  constructor
  · nlinarith [Real.log_two_gt_d9, logFiveWindow.1]
  · nlinarith [Real.log_two_lt_d9, logFiveWindow.2]

def sourceModel : OperationSemantics.Model ℝ :=
  { operation := sourceOperation, relation := fun inputs _ => inputs = [] }

def logModel : OperationSemantics.Model ℝ :=
  { operation := logOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = Real.log input
      | _ => False }

noncomputable def rowS (certificate : RowCertificate) (b : ℝ) : ℝ :=
  (decimalValue certificate.capital + 1) * Real.exp (-b / 2) +
    1.03883 * Real.exp (-2 * b / 3) +
    decimalValue certificate.c * Real.exp (-3 * b / 4) +
    1.03883 * Real.exp (-4 * b / 5)

noncomputable def rowValues (certificate : RowCertificate) (b : ℝ) : List ℝ :=
  [b ^ 1 * rowS certificate b, b ^ 2 * rowS certificate b,
    b ^ 3 * rowS certificate b, b ^ 4 * rowS certificate b,
    b ^ 5 * rowS certificate b]

def batchModel (operation : Operation) (certificate : RowCertificate) :
    OperationSemantics.Model ℝ :=
  { operation
    relation := fun inputs _ =>
      match inputs with
      | b :: values => values = rowValues certificate b
      | _ => False }

def operationModels : Array (OperationSemantics.Model ℝ) :=
  #[sourceModel, logModel, batchModel fiveBatchOperation fiveRow,
    batchModel thirtyTwoBatchOperation thirtyTwoRow]

def semantics : Semantics Bound :=
  OperationSemantics.semantics operationModels Contains

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

def RowHolds (certificate : RowCertificate) (b : ℝ) : Prop :=
  b ^ 1 * rowS certificate b ≤ decimalValue certificate.cell1 ∧
    b ^ 2 * rowS certificate b ≤ decimalValue certificate.cell2 ∧
    b ^ 3 * rowS certificate b ≤ decimalValue certificate.cell3 ∧
    b ^ 4 * rowS certificate b ≤ decimalValue certificate.cell4 ∧
    b ^ 5 * rowS certificate b ≤ decimalValue certificate.cell5

private theorem halfWindow : Real.exp (-(1 : ℝ) / 2) < 0.606530660 := by
  have remainder := Real.exp_bound
    (x := (-(1 : ℝ) / 2)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  linarith

private theorem twoThirdsWindow : Real.exp (-(2 : ℝ) / 3) < 0.513417120 := by
  have remainder := Real.exp_bound
    (x := (-(2 : ℝ) / 3)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  linarith

private theorem threeQuartersWindow : Real.exp (-(3 : ℝ) / 4) < 0.472366553 := by
  have remainder := Real.exp_bound
    (x := (-(3 : ℝ) / 4)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  linarith

private theorem fourFifthsWindow : Real.exp (-(4 : ℝ) / 5) < 0.449328965 := by
  have remainder := Real.exp_bound
    (x := (-(4 : ℝ) / 5)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  linarith

private theorem expUpper (x upper : ℝ) (bound : |x| ≤ 1) (checked :
    ∑ k ∈ Finset.range 14, x ^ k / Nat.factorial k +
        |x| ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) < upper) :
    Real.exp x < upper := by
  have remainder := Real.exp_bound (x := x) (n := 14) bound (by norm_num)
  rw [abs_le] at remainder
  linarith

private theorem fiveTailHalf : Real.exp (-(0.6352888 : ℝ) / 2) < 0.727861571 := by
  apply expUpper <;> norm_num [sum_range_succ]

private theorem fiveTailTwoThirds :
    Real.exp (-(2 * 0.6352888 : ℝ) / 3) < 0.654734241 := by
  apply expUpper <;> norm_num [sum_range_succ]

private theorem fiveTailThreeQuarters :
    Real.exp (-(3 * 0.6352888 : ℝ) / 4) < 0.620973670 := by
  apply expUpper <;> norm_num [sum_range_succ]

private theorem fiveTailFourFifths :
    Real.exp (-(4 * 0.6352888 : ℝ) / 5) < 0.601558773 := by
  apply expUpper <;> norm_num [sum_range_succ]

private theorem thirtyTwoTailHalf :
    Real.exp (-(0.0967570 : ℝ) / 2) < 0.952773096 := by
  apply expUpper <;> norm_num [sum_range_succ]

private theorem thirtyTwoTailTwoThirds :
    Real.exp (-(2 * 0.0967570 : ℝ) / 3) < 0.937531741 := by
  apply expUpper <;> norm_num [sum_range_succ]

private theorem thirtyTwoTailThreeQuarters :
    Real.exp (-(3 * 0.0967570 : ℝ) / 4) < 0.930002738 := by
  apply expUpper <;> norm_num [sum_range_succ]

private theorem thirtyTwoTailFourFifths :
    Real.exp (-(4 * 0.0967570 : ℝ) / 5) < 0.925514390 := by
  apply expUpper <;> norm_num [sum_range_succ]

private theorem splitExpUpper (n : Nat) (fraction q base tail : ℝ)
    (positive : n ≠ 0) (basePositive : 0 < base)
    (baseBound : Real.exp (-q) < base)
    (tailBound : Real.exp (-fraction * q) < tail) :
    Real.exp (-(n + fraction) * q) < base ^ n * tail := by
  rw [show -(n + fraction) * q = (n : ℝ) * (-q) + (-fraction * q) by ring,
    Real.exp_add]
  have power := pow_lt_pow_left₀ baseBound (Real.exp_pos (-q)).le positive
  rw [← Real.exp_nat_mul] at power
  exact mul_lt_mul power tailBound.le (Real.exp_pos _) (pow_pos basePositive n).le

private theorem rowBoundsOfChecked (certificate : RowCertificate) (b : ℝ)
    (lower : ℝ) (upper : ℝ) (hlo : lower ≤ b) (hhi : b ≤ upper)
    (lowerNonnegative : 0 ≤ lower)
    (exp1 : Real.exp (-lower / 2) ≤ 0.606530660 ^ certificate.floor *
      (match certificate.row with | .fiveE10 => 0.727861571 | .thirtyTwoE12 => 0.952773096))
    (exp2 : Real.exp (-2 * lower / 3) ≤ 0.513417120 ^ certificate.floor *
      (match certificate.row with | .fiveE10 => 0.654734241 | .thirtyTwoE12 => 0.937531741))
    (exp3 : Real.exp (-3 * lower / 4) ≤ 0.472366553 ^ certificate.floor *
      (match certificate.row with | .fiveE10 => 0.620973670 | .thirtyTwoE12 => 0.930002738))
    (exp4 : Real.exp (-4 * lower / 5) ≤ 0.449328965 ^ certificate.floor *
      (match certificate.row with | .fiveE10 => 0.601558773 | .thirtyTwoE12 => 0.925514390))
    (cNonnegative : 0 ≤ decimalValue certificate.c)
    (capitalNonnegative : 0 ≤ decimalValue certificate.capital)
    (checks :
      let rational :=
        (decimalValue certificate.capital + 1) *
            (0.606530660 ^ certificate.floor *
              (match certificate.row with | .fiveE10 => 0.727861571 | .thirtyTwoE12 => 0.952773096)) +
          1.03883 * (0.513417120 ^ certificate.floor *
              (match certificate.row with | .fiveE10 => 0.654734241 | .thirtyTwoE12 => 0.937531741)) +
          decimalValue certificate.c * (0.472366553 ^ certificate.floor *
              (match certificate.row with | .fiveE10 => 0.620973670 | .thirtyTwoE12 => 0.930002738)) +
          1.03883 * (0.449328965 ^ certificate.floor *
              (match certificate.row with | .fiveE10 => 0.601558773 | .thirtyTwoE12 => 0.925514390))
      upper ^ 1 * rational ≤ decimalValue certificate.cell1 ∧
        upper ^ 2 * rational ≤ decimalValue certificate.cell2 ∧
        upper ^ 3 * rational ≤ decimalValue certificate.cell3 ∧
        upper ^ 4 * rational ≤ decimalValue certificate.cell4 ∧
        upper ^ 5 * rational ≤ decimalValue certificate.cell5) :
    RowHolds certificate b := by
  let rational :=
    (decimalValue certificate.capital + 1) *
        (0.606530660 ^ certificate.floor *
          (match certificate.row with | .fiveE10 => 0.727861571 | .thirtyTwoE12 => 0.952773096)) +
      1.03883 * (0.513417120 ^ certificate.floor *
          (match certificate.row with | .fiveE10 => 0.654734241 | .thirtyTwoE12 => 0.937531741)) +
      decimalValue certificate.c * (0.472366553 ^ certificate.floor *
          (match certificate.row with | .fiveE10 => 0.620973670 | .thirtyTwoE12 => 0.930002738)) +
      1.03883 * (0.449328965 ^ certificate.floor *
          (match certificate.row with | .fiveE10 => 0.601558773 | .thirtyTwoE12 => 0.925514390))
  have shared : rowS certificate b ≤ rational := by
    have h1 := (Real.exp_le_exp.mpr (by linarith : -b / 2 ≤ -lower / 2)).trans exp1
    have h2 := (Real.exp_le_exp.mpr (by linarith : -2 * b / 3 ≤ -2 * lower / 3)).trans exp2
    have h3 := (Real.exp_le_exp.mpr (by linarith : -3 * b / 4 ≤ -3 * lower / 4)).trans exp3
    have h4 := (Real.exp_le_exp.mpr (by linarith : -4 * b / 5 ≤ -4 * lower / 5)).trans exp4
    unfold rowS rational
    have capitalPlus : 0 ≤ decimalValue certificate.capital + 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 capitalPlus,
      mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 1.03883),
      mul_le_mul_of_nonneg_left h3 cNonnegative,
      mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 1.03883)]
  have bNonnegative : 0 ≤ b := le_trans lowerNonnegative hlo
  have upperNonnegative : 0 ≤ upper := le_trans bNonnegative hhi
  have rowSNonnegative : 0 ≤ rowS certificate b := by
    unfold rowS
    have capitalPlus : 0 ≤ decimalValue certificate.capital + 1 := by linarith
    positivity
  have powers (k : Nat) : b ^ k ≤ upper ^ k := pow_le_pow_left₀ bNonnegative hhi k
  dsimp only at checks
  change RowHolds certificate b
  rcases checks with ⟨c1, c2, c3, c4, c5⟩
  constructor
  · exact le_trans (mul_le_mul (powers 1) shared rowSNonnegative
      (pow_nonneg upperNonnegative 1)) c1
  constructor
  · exact le_trans (mul_le_mul (powers 2) shared rowSNonnegative
      (pow_nonneg upperNonnegative 2)) c2
  constructor
  · exact le_trans (mul_le_mul (powers 3) shared rowSNonnegative
      (pow_nonneg upperNonnegative 3)) c3
  constructor
  · exact le_trans (mul_le_mul (powers 4) shared rowSNonnegative
      (pow_nonneg upperNonnegative 4)) c4
  · exact le_trans (mul_le_mul (powers 5) shared rowSNonnegative
      (pow_nonneg upperNonnegative 5)) c5

private theorem fiveRowBounds (b : ℝ)
    (hlo : decimalValue fiveRow.lower ≤ b)
    (hhi : b ≤ decimalValue fiveRow.upper) : RowHolds fiveRow b := by
  have hlo' : (24.6352888 : ℝ) ≤ b := by
    norm_num [fiveRow, decimalValue, decimal] at hlo ⊢
    exact hlo
  have hhi' : b ≤ (24.6352889 : ℝ) := by
    norm_num [fiveRow, decimalValue, decimal] at hhi ⊢
    exact hhi
  apply rowBoundsOfChecked fiveRow b (24.6352888 : ℝ) (24.6352889 : ℝ) hlo' hhi'
  · norm_num
  · have result := splitExpUpper 24 0.6352888 (1 / 2) 0.606530660 0.727861571
      (by norm_num) (by norm_num) (by convert halfWindow using 1 <;> ring_nf)
      (by convert fiveTailHalf using 1 <;> ring_nf)
    rw [show -((↑(24 : Nat) : ℝ) + 0.6352888) * (1 / 2) = -24.6352888 / 2 by norm_num] at result
    simpa [fiveRow] using result.le
  · have result := splitExpUpper 24 0.6352888 (2 / 3) 0.513417120 0.654734241
      (by norm_num) (by norm_num) (by convert twoThirdsWindow using 1 <;> ring_nf)
      (by convert fiveTailTwoThirds using 1 <;> ring_nf)
    rw [show -((↑(24 : Nat) : ℝ) + 0.6352888) * (2 / 3) = -2 * 24.6352888 / 3 by norm_num] at result
    simpa [fiveRow] using result.le
  · have result := splitExpUpper 24 0.6352888 (3 / 4) 0.472366553 0.620973670
      (by norm_num) (by norm_num) (by convert threeQuartersWindow using 1 <;> ring_nf)
      (by convert fiveTailThreeQuarters using 1 <;> ring_nf)
    rw [show -((↑(24 : Nat) : ℝ) + 0.6352888) * (3 / 4) = -3 * 24.6352888 / 4 by norm_num] at result
    simpa [fiveRow] using result.le
  · have result := splitExpUpper 24 0.6352888 (4 / 5) 0.449328965 0.601558773
      (by norm_num) (by norm_num) (by convert fourFifthsWindow using 1 <;> ring_nf)
      (by convert fiveTailFourFifths using 1 <;> ring_nf)
    rw [show -((↑(24 : Nat) : ℝ) + 0.6352888) * (4 / 5) = -4 * 24.6352888 / 5 by norm_num] at result
    simpa [fiveRow] using result.le
  · norm_num [fiveRow, decimalValue, decimal]
  · norm_num [fiveRow, decimalValue, decimal]
  · norm_num [fiveRow, decimalValue, decimal]

private theorem thirtyTwoRowBounds (b : ℝ)
    (hlo : decimalValue thirtyTwoRow.lower ≤ b)
    (hhi : b ≤ decimalValue thirtyTwoRow.upper) : RowHolds thirtyTwoRow b := by
  have hlo' : (31.0967570 : ℝ) ≤ b := by
    norm_num [thirtyTwoRow, decimalValue, decimal] at hlo ⊢
    exact hlo
  have hhi' : b ≤ (31.0967571 : ℝ) := by
    norm_num [thirtyTwoRow, decimalValue, decimal] at hhi ⊢
    exact hhi
  apply rowBoundsOfChecked thirtyTwoRow b (31.0967570 : ℝ) (31.0967571 : ℝ) hlo' hhi'
  · norm_num
  · have result := splitExpUpper 31 0.0967570 (1 / 2) 0.606530660 0.952773096
      (by norm_num) (by norm_num) (by convert halfWindow using 1 <;> ring_nf)
      (by convert thirtyTwoTailHalf using 1 <;> ring_nf)
    rw [show -((↑(31 : Nat) : ℝ) + 0.0967570) * (1 / 2) = -31.0967570 / 2 by norm_num] at result
    simpa [thirtyTwoRow] using result.le
  · have result := splitExpUpper 31 0.0967570 (2 / 3) 0.513417120 0.937531741
      (by norm_num) (by norm_num) (by convert twoThirdsWindow using 1 <;> ring_nf)
      (by convert thirtyTwoTailTwoThirds using 1 <;> ring_nf)
    rw [show -((↑(31 : Nat) : ℝ) + 0.0967570) * (2 / 3) = -2 * 31.0967570 / 3 by norm_num] at result
    simpa [thirtyTwoRow] using result.le
  · have result := splitExpUpper 31 0.0967570 (3 / 4) 0.472366553 0.930002738
      (by norm_num) (by norm_num) (by convert threeQuartersWindow using 1 <;> ring_nf)
      (by convert thirtyTwoTailThreeQuarters using 1 <;> ring_nf)
    rw [show -((↑(31 : Nat) : ℝ) + 0.0967570) * (3 / 4) = -3 * 31.0967570 / 4 by norm_num] at result
    simpa [thirtyTwoRow] using result.le
  · have result := splitExpUpper 31 0.0967570 (4 / 5) 0.449328965 0.925514390
      (by norm_num) (by norm_num) (by convert fourFifthsWindow using 1 <;> ring_nf)
      (by convert thirtyTwoTailFourFifths using 1 <;> ring_nf)
    rw [show -((↑(31 : Nat) : ℝ) + 0.0967570) * (4 / 5) = -4 * 31.0967570 / 5 by norm_num] at result
    simpa [thirtyTwoRow] using result.le
  · norm_num [thirtyTwoRow, decimalValue, decimal]
  · norm_num [thirtyTwoRow, decimalValue, decimal]
  · norm_num [thirtyTwoRow, decimalValue, decimal]

private theorem operationOutput (graph : Program) (valuation : NodeId → ℝ)
    (models : OperationSemantics.Models operationModels graph valuation)
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input]) :
    valuation output = Real.log (valuation input) := by
  obtain ⟨meaning, meaningAt, related⟩ := models.2 output instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  simpa [logModel, arguments, List.map] using related

private theorem windowEntails (certificate : RowCertificate)
    (checked : decimalValue certificate.lower ≤ Real.log (decimalValue certificate.input) ∧
      Real.log (decimalValue certificate.input) ≤ decimalValue certificate.upper)
    (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (inputFacts : assumptions =
      [{ node := input, fact := Bound.point certificate.input }]) :
    semantics.Entails graph assumptions
      { node := output, fact := Bound.window certificate.lower certificate.upper } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains (Bound.window certificate.lower certificate.upper) (valuation output)
  intro valuation models holds
  have point := holds { node := input, fact := Bound.point certificate.input }
    (by simp [inputFacts])
  have inputExact : valuation input = decimalValue certificate.input := by
    change decimalValue certificate.input ≤ valuation input ∧
      valuation input ≤ decimalValue certificate.input at point
    linarith
  have outputEq := operationOutput graph valuation models output instruction input
    found operation arguments
  change decimalValue certificate.lower ≤ valuation output ∧
    valuation output ≤ decimalValue certificate.upper
  simpa [outputEq, inputExact] using checked

private theorem forall₂RightGet {relation : α → β → Prop}
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

private theorem rowCellsBounds (certificate : RowCertificate) (b : ℝ)
    (bounds : RowHolds certificate b) :
    List.Forall₂ (· ≤ decimalValue ·.cut) (rowValues certificate b)
      certificate.cells := by
  rcases bounds with ⟨h1, h2, h3, h4, h5⟩
  unfold rowValues RowCertificate.cells
  exact .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 .nil))))

private theorem cellFromValues (certificate : RowCertificate) (b : ℝ)
    (valuation : NodeId → ℝ) (instruction : Node) (target : NodeId)
    (cell : CellCertificate) (index : Nat)
    (values : instruction.args.map valuation = b :: rowValues certificate b)
    (targetFound : instruction.args[index + 1]? = some target)
    (cellFound : certificate.cells[index]? = some cell)
    (bounds : RowHolds certificate b) :
    valuation target ≤ decimalValue cell.cut := by
  have mapped : (instruction.args.map valuation)[index + 1]? =
      some (valuation target) := by simp [targetFound]
  have rowFound : (rowValues certificate b)[index]? = some (valuation target) := by
    rw [values] at mapped
    simpa using mapped
  obtain ⟨input, inputFound, inputBound⟩ :=
    forall₂RightGet (rowCellsBounds certificate b bounds) index cell cellFound
  have equal : valuation target = input :=
    Option.some.inj (rowFound.symm.trans inputFound)
  simpa [equal] using inputBound

private theorem fiveCellEntails (graph : Program)
    (assumptions : List (NodeFact Bound)) (anchor : NodeId)
    (instruction : Node) (input target : NodeId) (cell : CellCertificate)
    (index : Nat) (found : graph.node? anchor = some instruction)
    (operation : instruction.op = { index := 2 })
    (arguments : instruction.args = input :: fiveCellNodes)
    (targetFound : instruction.args[index + 1]? = some target)
    (cellFound : fiveRow.cells[index]? = some cell)
    (inputFacts : assumptions =
      [{ node := input, fact := Bound.window fiveRow.lower fiveRow.upper }]) :
    semantics.Entails graph assumptions { node := target, fact := Bound.upper cell.cut } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains (Bound.upper cell.cut) (valuation target)
  intro valuation models holds
  have window := holds
    { node := input, fact := Bound.window fiveRow.lower fiveRow.upper }
    (by simp [inputFacts])
  obtain ⟨meaning, meaningAt, related⟩ := models.2 anchor instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have tails : fiveCellNodes.map valuation = rowValues fiveRow (valuation input) := by
    simpa [batchModel, arguments] using related
  have values : instruction.args.map valuation =
      valuation input :: rowValues fiveRow (valuation input) := by
    simp [arguments, tails]
  simpa [Contains, Bound.upper, lowerContains, upperContains] using
    cellFromValues fiveRow (valuation input) valuation instruction target cell index
      values targetFound cellFound (fiveRowBounds (valuation input) window.1 window.2)

private theorem thirtyTwoCellEntails (graph : Program)
    (assumptions : List (NodeFact Bound)) (anchor : NodeId)
    (instruction : Node) (input target : NodeId) (cell : CellCertificate)
    (index : Nat) (found : graph.node? anchor = some instruction)
    (operation : instruction.op = { index := 3 })
    (arguments : instruction.args = input :: thirtyTwoCellNodes)
    (targetFound : instruction.args[index + 1]? = some target)
    (cellFound : thirtyTwoRow.cells[index]? = some cell)
    (inputFacts : assumptions =
      [{ node := input, fact := Bound.window thirtyTwoRow.lower thirtyTwoRow.upper }]) :
    semantics.Entails graph assumptions { node := target, fact := Bound.upper cell.cut } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains (Bound.upper cell.cut) (valuation target)
  intro valuation models holds
  have window := holds
    { node := input, fact := Bound.window thirtyTwoRow.lower thirtyTwoRow.upper }
    (by simp [inputFacts])
  obtain ⟨meaning, meaningAt, related⟩ := models.2 anchor instruction found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have tails : thirtyTwoCellNodes.map valuation =
      rowValues thirtyTwoRow (valuation input) := by
    simpa [batchModel, arguments] using related
  have values : instruction.args.map valuation =
      valuation input :: rowValues thirtyTwoRow (valuation input) := by
    simp [arguments, tails]
  simpa [Contains, Bound.upper, lowerContains, upperContains] using
    cellFromValues thirtyTwoRow (valuation input) valuation instruction target cell index
      values targetFound cellFound (thirtyTwoRowBounds (valuation input) window.1 window.2)

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) : fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

def windowFactSchema : PackedFactSchema semantics where
  rule := logRuleKey
  schema := 1
  Certificate := LogRow
  decode := decodeWindow?
  replay := fun _ _ context certificate =>
    match found : context.program.node? context.proposed.node with
    | some instruction =>
        if operation : instruction.op = ({ index := 1 } : OpId) then
          match arguments : instruction.args with
          | [input] =>
              match certificate with
              | .fiveE10 =>
                  if proposedFact : context.proposed.fact =
                      Bound.window fiveRow.lower fiveRow.upper then
                    if inputFacts : context.assumptions =
                        [{ node := input, fact := Bound.point fiveRow.input }] then
                      some
                        { proof := by
                            rw [factWith context.proposed proposedFact]
                            apply windowEntails fiveRow
                            · constructor
                              · norm_num [fiveRow, decimalValue, decimal]
                                nlinarith [logFiveE10Window.1]
                              · norm_num [fiveRow, decimalValue, decimal]
                                nlinarith [logFiveE10Window.2]
                            · exact found
                            · exact operation
                            · exact arguments
                            · exact inputFacts }
                    else none
                  else none
              | .thirtyTwoE12 =>
                  if proposedFact : context.proposed.fact =
                      Bound.window thirtyTwoRow.lower thirtyTwoRow.upper then
                    if inputFacts : context.assumptions =
                        [{ node := input, fact := Bound.point thirtyTwoRow.input }] then
                      some
                        { proof := by
                            rw [factWith context.proposed proposedFact]
                            apply windowEntails thirtyTwoRow
                            · constructor
                              · norm_num [thirtyTwoRow, decimalValue, decimal]
                                nlinarith [logThirtyTwoE12Window.1]
                              · norm_num [thirtyTwoRow, decimalValue, decimal]
                                nlinarith [logThirtyTwoE12Window.2]
                            · exact found
                            · exact operation
                            · exact arguments
                            · exact inputFacts }
                    else none
                  else none
          | _ => none
        else none
    | none => none

def rowFactSchema (certificate : RowCertificate) (ruleKey : RuleKey)
    (operationIndex : Nat) : PackedFactSchema semantics where
  rule := ruleKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body == rowBody certificate then some () else none
  replay := fun _ action context _ =>
    match found : context.program.node? action.node with
    | some instruction =>
        if operation : instruction.op = ({ index := operationIndex } : OpId) then
          match arguments : instruction.args with
          | input :: _ =>
              if argumentExact : instruction.args = input ::
                  (match certificate.row with
                    | .fiveE10 => fiveCellNodes | .thirtyTwoE12 => thirtyTwoCellNodes) then
                if inputFacts : context.assumptions =
                    [{ node := input, fact := Bound.window certificate.lower certificate.upper }] then
                  let index := context.proposed.node.index - 4 -
                    (match certificate.row with | .fiveE10 => 0 | .thirtyTwoE12 => 5)
                  match cellFound : certificate.cells[index]? with
                  | some cell =>
                      if proposedFact : context.proposed.fact = Bound.upper cell.cut then
                        if targetFound : instruction.args[index + 1]? =
                            some context.proposed.node then
                          match certificate.row with
                          | .fiveE10 =>
                              if certificateExact : certificate = fiveRow then
                                if operationExact : operationIndex = 2 then
                                  some
                                    { proof := by
                                        subst certificate
                                        subst operationIndex
                                        rw [factWith context.proposed proposedFact]
                                        exact fiveCellEntails context.program context.assumptions
                                          action.node instruction input context.proposed.node cell
                                          index found operation argumentExact targetFound cellFound
                                          inputFacts }
                                else none
                              else none
                          | .thirtyTwoE12 =>
                              if certificateExact : certificate = thirtyTwoRow then
                                if operationExact : operationIndex = 3 then
                                  some
                                    { proof := by
                                        subst certificate
                                        subst operationIndex
                                        rw [factWith context.proposed proposedFact]
                                        exact thirtyTwoCellEntails context.program context.assumptions
                                          action.node instruction input context.proposed.node cell
                                          index found operation argumentExact targetFound cellFound
                                          inputFacts }
                                else none
                              else none
                        else none
                      else none
                  | none => none
                else none
              else none
          | [] => none
        else none
    | none => none

def fiveFactSchema : PackedFactSchema semantics := rowFactSchema fiveRow fiveRuleKey 2
def thirtyTwoFactSchema : PackedFactSchema semantics :=
  rowFactSchema thirtyTwoRow thirtyTwoRuleKey 3

def stableLaw : StableLaw semantics :=
  OperationSemantics.stableLaw operationModels Contains

def sourceEmit : EmitPackage Lean.Name := { schemas := [] }
def logEmit : EmitPackage Lean.Name :=
  { schemas := [{ key := windowFactSchema.key, handle := ``windowFactSchema }] }
def rowEmit : EmitPackage Lean.Name :=
  { schemas := [{ key := fiveFactSchema.key, handle := ``fiveFactSchema },
      { key := thirtyTwoFactSchema.key, handle := ``thirtyTwoFactSchema }] }

def sourceProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[] }, emit := sourceEmit }
def logProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[windowFactSchema] }, emit := logEmit }
def rowProof : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[fiveFactSchema, thirtyTwoFactSchema] }, emit := rowEmit }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, logProof, rowProof]

/-! # Exact source-list boundary -/

abbrev TableRow := ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ

inductive TableCertificate where
  | ordinary (certificate : PntTable12Ordinary.RowCertificate)
  | row25
  | logarithmic (certificate : RowCertificate)

def tableCertificates : List TableCertificate :=
  (PntTable12Ordinary.ordinaryRows.take 5).map .ordinary ++
    [.logarithmic fiveRow, .row25] ++
    ((PntTable12Ordinary.ordinaryRows.drop 5).take 6).map .ordinary ++
    [.logarithmic thirtyTwoRow] ++
    (PntTable12Ordinary.ordinaryRows.drop 11).map .ordinary

noncomputable def TableCertificate.tuple : TableCertificate → TableRow
  | .ordinary certificate =>
      (certificate.row, PntTable12Ordinary.Decimal.value certificate.cell1,
        PntTable12Ordinary.Decimal.value certificate.cell2,
        PntTable12Ordinary.Decimal.value certificate.cell3,
        PntTable12Ordinary.Decimal.value certificate.cell4,
        PntTable12Ordinary.Decimal.value certificate.cell5,
        PntTable12Ordinary.Decimal.value certificate.c,
        PntTable12Ordinary.Decimal.value certificate.capital,
        certificate.mMantissa * (10 : ℝ) ^ certificate.mExponent)
  | .row25 =>
      (25, 1.750020e-4, 4.375050e-3, 1.093770e-1, 2.734410e0,
        6.836010e1, 0.88, 0.86, 32e12)
  | .logarithmic certificate =>
      (Real.log (decimalValue certificate.input), decimalValue certificate.cell1,
        decimalValue certificate.cell2, decimalValue certificate.cell3,
        decimalValue certificate.cell4, decimalValue certificate.cell5,
        decimalValue certificate.c, decimalValue certificate.capital,
        certificate.mMantissa * (10 : ℝ) ^ certificate.mExponent)

noncomputable def table12 : List TableRow :=
  tableCertificates.map TableCertificate.tuple

noncomputable def tableS (b c capital : ℝ) : ℝ :=
  (capital + 1) * Real.exp (-b / 2) +
    1.03883 * Real.exp (-2 * b / 3) +
    c * Real.exp (-3 * b / 4) +
    1.03883 * Real.exp (-4 * b / 5)

def TableCheck : TableRow → Prop
  | (b, cell1, cell2, cell3, cell4, cell5, c, capital, _) =>
      b ^ 1 * tableS b c capital ≤ cell1 ∧
        b ^ 2 * tableS b c capital ≤ cell2 ∧
        b ^ 3 * tableS b c capital ≤ cell3 ∧
        b ^ 4 * tableS b c capital ≤ cell4 ∧
        b ^ 5 * tableS b c capital ≤ cell5

def TableCertificate.Holds : TableCertificate → Prop
  | .ordinary certificate => PntTable12Ordinary.RowHolds certificate
  | .row25 =>
      PntTable12.row25Value 1 ≤ 175002 / 1000000000 ∧
        PntTable12.row25Value 2 ≤ 437505 / 100000000 ∧
        PntTable12.row25Value 3 ≤ 109377 / 1000000 ∧
        PntTable12.row25Value 4 ≤ 273441 / 100000 ∧
        PntTable12.row25Value 5 ≤ 683601 / 10000
  | .logarithmic certificate =>
      RowHolds certificate (Real.log (decimalValue certificate.input))

theorem tableCertificatesHold (certificate : TableCertificate)
    (member : certificate ∈ tableCertificates) : certificate.Holds := by
  cases certificate with
  | ordinary certificate =>
      apply PntTable12Ordinary.ordinaryRowsBounds certificate
      simp [tableCertificates, PntTable12Ordinary.ordinaryRows] at member ⊢
      aesop
  | row25 => exact PntTable12.row25Bounds
  | logarithmic certificate =>
      simp [tableCertificates, PntTable12Ordinary.ordinaryRows] at member
      rcases member with rfl | rfl
      · exact fiveRowBounds _
          (by
            norm_num [fiveRow, decimalValue, decimal]
            nlinarith [logFiveE10Window.1])
          (by
            norm_num [fiveRow, decimalValue, decimal]
            nlinarith [logFiveE10Window.2])
      · exact thirtyTwoRowBounds _
          (by
            norm_num [thirtyTwoRow, decimalValue, decimal]
            nlinarith [logThirtyTwoE12Window.1])
          (by
            norm_num [thirtyTwoRow, decimalValue, decimal]
            nlinarith [logThirtyTwoE12Window.2])

theorem certificateCheck (certificate : TableCertificate)
    (holds : certificate.Holds) : TableCheck certificate.tuple := by
  cases certificate with
  | ordinary certificate =>
      simpa [TableCheck, TableCertificate.tuple, TableCertificate.Holds,
        tableS, PntTable12Ordinary.RowHolds, PntTable12Ordinary.rowValue,
        PntTable12Ordinary.rowS] using holds
  | row25 =>
      simp only [TableCheck, TableCertificate.tuple]
      rw [show tableS 25 0.88 0.86 = PntTable12.row25S by
        unfold tableS PntTable12.row25S
        congr 1 <;> ring]
      norm_num [TableCertificate.Holds, PntTable12.row25Value] at holds ⊢
      exact holds
  | logarithmic certificate =>
      simpa [TableCheck, TableCertificate.tuple, TableCertificate.Holds,
        tableS, RowHolds, rowS] using holds

/-- Source-shaped arbitrary-membership wrapper for all 130 numerical leaves. -/
theorem table12Check (b cell1 cell2 cell3 cell4 cell5 c capital m : ℝ)
    (member : (b, cell1, cell2, cell3, cell4, cell5, c, capital, m) ∈ table12) :
    b ^ 1 * tableS b c capital ≤ cell1 ∧
      b ^ 2 * tableS b c capital ≤ cell2 ∧
      b ^ 3 * tableS b c capital ≤ cell3 ∧
      b ^ 4 * tableS b c capital ≤ cell4 ∧
      b ^ 5 * tableS b c capital ≤ cell5 := by
  obtain ⟨certificate, certificateMember, equal⟩ := List.mem_map.mp member
  have checked := certificateCheck certificate
    (tableCertificatesHold certificate certificateMember)
  rw [equal] at checked
  exact checked

end Hex.Interval.Experiment.PntTable12Log
