/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntTable10Shard
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

/-!
# Ordinary-kernel semantics for the BKLNW Table 10 shard

The checked row payload is interpreted as the five endpoint maxima of the
coefficient majorant used by pinned PNT+ for row 25.  Convexity turns those
endpoint facts into bounds throughout `[25,26]`.  This is the exact bridge
needed by PNT+'s existing `row_bound_k1`/`row_bound_kge2` reduction; it does not
copy LeanCert's API or claim the other 286 Table 10 rows.
-/

namespace Hex.Interval.Experiment.PntTable10Shard

open Real Set Finset
open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

noncomputable def Decimal.value (value : Decimal) : ℝ :=
  value.mantissa / (10 : ℝ) ^ value.scale

theorem decimalMulValue (left right : Decimal) :
    (left.mul right).value = left.value * right.value := by
  unfold Decimal.mul Decimal.value decimal
  rw [pow_add]
  push_cast
  field_simp

theorem decimalAddValue (left right : Decimal) :
    (left.add right).value = left.value + right.value := by
  unfold Decimal.add Decimal.value decimal
  rw [pow_add]
  push_cast
  field_simp

theorem decimalPowNatValue (base power : Nat) :
    (Decimal.powNat base power).value = (base : ℝ) ^ power := by
  simp [Decimal.powNat, Decimal.value, decimal]

theorem decimalLe_iff (left right : Decimal) :
    left.le right ↔ left.value ≤ right.value := by
  unfold Decimal.le Decimal.value
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ left.scale)
    (by positivity : (0 : ℝ) < 10 ^ right.scale)]
  simp only [decide_eq_true_eq]
  constructor <;> intro comparison <;> exact_mod_cast comparison

noncomputable def majorant (column : Nat) (y : ℝ) : ℝ :=
  certificate.a1.value * y ^ column * Real.exp (-(y / 2)) +
    certificate.a2.value * y ^ column * Real.exp (-(2 * y / 3)) +
    certificate.epsilon.value * y ^ column

noncomputable def endpointValue (cell : Cell) : ℝ :=
  max (majorant cell.coordinate.column certificate.row)
    (majorant cell.coordinate.column certificate.nextRow)

noncomputable def endpointValues : List ℝ :=
  certificate.cells.map endpointValue

def sourceModel : OperationSemantics.Model ℝ :=
  { operation := sourceOperation, relation := fun inputs _ => inputs = [] }

def batchModel : OperationSemantics.Model ℝ :=
  { operation := batchOperation, relation := fun inputs _ => inputs = endpointValues }

def operationModels : Array (OperationSemantics.Model ℝ) := #[sourceModel, batchModel]

def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .upper cell, value => value ≤ cell.target.value
  | .empty, _ => False

theorem containsMeet (left right : Bound) (value : ℝ) :
    Contains (left.meet right) value ↔ Contains left value ∧ Contains right value := by
  cases left with
  | all => cases right <;> simp [Bound.meet, Contains]
  | empty => cases right <;> simp [Bound.meet, Contains]
  | upper left =>
      cases right with
      | all => simp [Bound.meet, Contains]
      | empty => simp [Bound.meet, Contains]
      | upper right =>
          simp only [Bound.meet]
          split <;> rename_i comparison
          · have tighter : left.target.value ≤ right.target.value :=
              decimalLe_iff left.target right.target |>.mp (by
                simpa using comparison)
            simp only [Contains]
            exact ⟨fun upper => ⟨upper, upper.trans tighter⟩, fun both => both.1⟩
          · have tighter : right.target.value ≤ left.target.value := by
              apply le_of_not_ge
              intro le
              exact comparison ((decimalLe_iff left.target right.target).mpr le)
            simp only [Contains]
            exact ⟨fun upper => ⟨upper.trans tighter, upper⟩, fun both => both.2⟩

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

private theorem halfUpper : Real.exp (-(1 : ℝ) / 2) < 0.606530660 := by
  have remainder := Real.exp_bound
    (x := (-(1 : ℝ) / 2)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  linarith

private theorem halfLower : (0.606530659 : ℝ) < Real.exp (-(1 : ℝ) / 2) := by
  have remainder := Real.exp_bound
    (x := (-(1 : ℝ) / 2)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  linarith

private theorem twoThirdUpper : Real.exp (-(2 : ℝ) / 3) < 0.513417120 := by
  have remainder := Real.exp_bound
    (x := (-(2 : ℝ) / 3)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  linarith

private theorem twoThirdLower :
    (0.513417119 : ℝ) < Real.exp (-(2 : ℝ) / 3) := by
  have remainder := Real.exp_bound
    (x := (-(2 : ℝ) / 3)) (n := 14) (by norm_num) (by norm_num)
  rw [abs_le] at remainder
  norm_num [sum_range_succ] at remainder ⊢
  linarith

private theorem expTermsUpper (b : Nat) (positive : b ≠ 0) :
    Real.exp (-(b : ℝ) / 2) < (0.606530660 : ℝ) ^ b ∧
      Real.exp (-(2 * b : ℝ) / 3) < (0.513417120 : ℝ) ^ b := by
  have half := pow_lt_pow_left₀ halfUpper
    (Real.exp_pos (-(1 : ℝ) / 2)).le positive
  have twoThird := pow_lt_pow_left₀ twoThirdUpper
    (Real.exp_pos (-(2 : ℝ) / 3)).le positive
  rw [← Real.exp_nat_mul] at half twoThird
  constructor
  · rw [show -(b : ℝ) / 2 = (b : ℝ) * (-(1 : ℝ) / 2) by ring]
    exact half
  · rw [show -(2 * b : ℝ) / 3 = (b : ℝ) * (-(2 : ℝ) / 3) by ring]
    exact twoThird

private theorem expTermsLower (b : Nat) (positive : b ≠ 0) :
    (0.606530659 : ℝ) ^ b < Real.exp (-(b : ℝ) / 2) ∧
      (0.513417119 : ℝ) ^ b < Real.exp (-(2 * b : ℝ) / 3) := by
  have half := pow_lt_pow_left₀ halfLower (by norm_num) positive
  have twoThird := pow_lt_pow_left₀ twoThirdLower (by norm_num) positive
  rw [← Real.exp_nat_mul] at half twoThird
  constructor
  · rw [show -(b : ℝ) / 2 = (b : ℝ) * (-(1 : ℝ) / 2) by ring]
    exact half
  · rw [show -(2 * b : ℝ) / 3 = (b : ℝ) * (-(2 : ℝ) / 3) by ring]
    exact twoThird

private theorem row25Windows :
    Real.exp (-(25 : ℝ) / 2) < certificate.halfLeft.value ∧
      Real.exp (-(2 * 25 : ℝ) / 3) < certificate.twoThirdLeft.value := by
  have windows := expTermsUpper 25 (by norm_num)
  norm_num [certificate, Decimal.value, decimal] at windows ⊢
  constructor <;> nlinarith [windows.1, windows.2]

private theorem row26Windows :
    Real.exp (-(26 : ℝ) / 2) < certificate.halfRight.value ∧
      Real.exp (-(2 * 26 : ℝ) / 3) < certificate.twoThirdRight.value := by
  have windows := expTermsUpper 26 (by norm_num)
  norm_num [certificate, Decimal.value, decimal] at windows ⊢
  constructor <;> nlinarith [windows.1, windows.2]

theorem endpointUpper (cell : Cell) (member : cell ∈ certificate.cells) :
    endpointValue cell ≤ cell.target.value := by
  have half25 : Real.exp (-(25 : ℝ) / 2) < (3728 / 10 ^ 9 : ℝ) := by
    simpa [certificate, Decimal.value, decimal] using row25Windows.1
  have twoThird25 : Real.exp (-(2 * 25 : ℝ) / 3) < (5779 / 10 ^ 11 : ℝ) := by
    simpa [certificate, Decimal.value, decimal] using row25Windows.2
  have half26 : Real.exp (-(26 : ℝ) / 2) < (2262 / 10 ^ 9 : ℝ) := by
    simpa [certificate, Decimal.value, decimal] using row26Windows.1
  have twoThird26 : Real.exp (-(2 * 26 : ℝ) / 3) < (2968 / 10 ^ 11 : ℝ) := by
    simpa [certificate, Decimal.value, decimal] using row26Windows.2
  simp only [Certificate.cells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold endpointValue majorant
    rw [max_le_iff]
    constructor
    · norm_num [certificate, sourceCell, corrected, margin, Decimal.mul,
        Decimal.value, decimal]
      nlinarith [half25, twoThird25,
        Real.exp_pos (-(25 : ℝ) / 2), Real.exp_pos (-(2 * 25 : ℝ) / 3)]
    · norm_num [certificate, sourceCell, corrected, margin, Decimal.mul,
        Decimal.value, decimal]
      nlinarith [half26, twoThird26,
        Real.exp_pos (-(26 : ℝ) / 2), Real.exp_pos (-(2 * 26 : ℝ) / 3)]

noncomputable def eT (c y : ℝ) : ℝ := y * Real.exp (-(c * y))
noncomputable def eTd (c y : ℝ) : ℝ := (1 - c * y) * Real.exp (-(c * y))
noncomputable def eTdd (c y : ℝ) : ℝ :=
  (c ^ 2 * y - 2 * c) * Real.exp (-(c * y))

private theorem eT_hasDerivAt (c y : ℝ) : HasDerivAt (eT c) (eTd c y) y := by
  unfold eT eTd
  have linear : HasDerivAt (fun u : ℝ => -(c * u)) (-(c * 1)) y :=
    ((hasDerivAt_id y).const_mul c).neg
  have exponential : HasDerivAt (fun u : ℝ => Real.exp (-(c * u)))
      (Real.exp (-(c * y)) * (-(c * 1))) y := linear.exp
  convert! (hasDerivAt_id y).mul exponential using 1
  simp only [id_eq]
  ring

private theorem eTd_hasDerivAt (c y : ℝ) : HasDerivAt (eTd c) (eTdd c y) y := by
  unfold eTd eTdd
  have polynomial : HasDerivAt (fun u : ℝ => 1 - c * u) (-(c * 1)) y := by
    convert! (hasDerivAt_const y (1 : ℝ)).sub
      ((hasDerivAt_id y).const_mul c) using 1
    ring
  have linear : HasDerivAt (fun u : ℝ => -(c * u)) (-(c * 1)) y :=
    ((hasDerivAt_id y).const_mul c).neg
  have exponential : HasDerivAt (fun u : ℝ => Real.exp (-(c * u)))
      (Real.exp (-(c * y)) * (-(c * 1))) y := linear.exp
  convert! polynomial.mul exponential using 1
  ring

noncomputable def G1 (A1 A2 E y : ℝ) : ℝ :=
  A1 * eT (1 / 2) y + A2 * eT (2 / 3) y + E * y
noncomputable def G1' (A1 A2 E y : ℝ) : ℝ :=
  A1 * eTd (1 / 2) y + A2 * eTd (2 / 3) y + E
noncomputable def G1'' (A1 A2 _E y : ℝ) : ℝ :=
  A1 * eTdd (1 / 2) y + A2 * eTdd (2 / 3) y

private theorem G1_hasDerivAt (A1 A2 E y : ℝ) :
    HasDerivAt (G1 A1 A2 E) (G1' A1 A2 E y) y := by
  unfold G1 G1'
  have h1 := (eT_hasDerivAt (1 / 2) y).const_mul A1
  have h2 := (eT_hasDerivAt (2 / 3) y).const_mul A2
  have h3 : HasDerivAt (fun u : ℝ => E * u) E y := by
    simpa using (hasDerivAt_id y).const_mul E
  convert! (h1.add h2).add h3 using 1

private theorem G1'_hasDerivAt (A1 A2 E y : ℝ) :
    HasDerivAt (G1' A1 A2 E) (G1'' A1 A2 E y) y := by
  unfold G1' G1''
  have h1 := (eTd_hasDerivAt (1 / 2) y).const_mul A1
  have h2 := (eTd_hasDerivAt (2 / 3) y).const_mul A2
  have h3 : HasDerivAt (fun _ : ℝ => E) 0 y := hasDerivAt_const y E
  convert! (h1.add h2).add h3 using 1
  all_goals ring

private theorem G1_convexOn {A1 A2 E : ℝ} (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) :
    ConvexOn ℝ (Icc 25 26) (G1 A1 A2 E) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (by unfold G1 eT; fun_prop : Continuous (G1 A1 A2 E)).continuousOn
  · intro y _
    exact (G1_hasDerivAt A1 A2 E y).hasDerivWithinAt
  · intro y _
    exact (G1'_hasDerivAt A1 A2 E y).hasDerivWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    unfold G1'' eTdd
    have first : 0 ≤ A1 * (((1 / 2 : ℝ) ^ 2 * y - 2 * (1 / 2)) *
        Real.exp (-((1 / 2 : ℝ) * y))) := by
      apply mul_nonneg hA1
      apply mul_nonneg _ (Real.exp_pos _).le
      nlinarith [hy.1]
    have second : 0 ≤ A2 * (((2 / 3 : ℝ) ^ 2 * y - 2 * (2 / 3)) *
        Real.exp (-((2 / 3 : ℝ) * y))) := by
      apply mul_nonneg hA2
      apply mul_nonneg _ (Real.exp_pos _).le
      nlinarith [hy.1]
    linarith

noncomputable def pT (m : Nat) (c y : ℝ) : ℝ :=
  y ^ (m + 2) * Real.exp (-(c * y))
noncomputable def pTd (m : Nat) (c y : ℝ) : ℝ :=
  (((m + 2 : Nat) : ℝ) * y ^ (m + 1) - c * y ^ (m + 2)) *
    Real.exp (-(c * y))
noncomputable def pTdd (m : Nat) (c y : ℝ) : ℝ :=
  (c ^ 2 * y ^ (m + 2) - 2 * c * ((m + 2 : Nat) : ℝ) * y ^ (m + 1) +
    ((m + 2 : Nat) : ℝ) * ((m + 1 : Nat) : ℝ) * y ^ m) *
      Real.exp (-(c * y))

private theorem pT_hasDerivAt (m : Nat) (c y : ℝ) :
    HasDerivAt (pT m c) (pTd m c y) y := by
  unfold pT pTd
  have power : HasDerivAt (fun u : ℝ => u ^ (m + 2))
      (((m + 2 : Nat) : ℝ) * y ^ (m + 1)) y := hasDerivAt_pow (m + 2) y
  have linear : HasDerivAt (fun u : ℝ => -(c * u)) (-(c * 1)) y :=
    ((hasDerivAt_id y).const_mul c).neg
  have exponential : HasDerivAt (fun u : ℝ => Real.exp (-(c * u)))
      (Real.exp (-(c * y)) * (-(c * 1))) y := linear.exp
  convert! power.mul exponential using 1
  ring

private theorem pTd_hasDerivAt (m : Nat) (c y : ℝ) :
    HasDerivAt (pTd m c) (pTdd m c y) y := by
  unfold pTd pTdd
  have polynomial : HasDerivAt
      (fun u : ℝ => ((m + 2 : Nat) : ℝ) * u ^ (m + 1) - c * u ^ (m + 2))
      (((m + 2 : Nat) : ℝ) * (((m + 1 : Nat) : ℝ) * y ^ m) -
        c * (((m + 2 : Nat) : ℝ) * y ^ (m + 1))) y := by
    exact ((hasDerivAt_pow (m + 1) y).const_mul _).sub
      ((hasDerivAt_pow (m + 2) y).const_mul _)
  have linear : HasDerivAt (fun u : ℝ => -(c * u)) (-(c * 1)) y :=
    ((hasDerivAt_id y).const_mul c).neg
  have exponential : HasDerivAt (fun u : ℝ => Real.exp (-(c * u)))
      (Real.exp (-(c * y)) * (-(c * 1))) y := linear.exp
  convert! polynomial.mul exponential using 1
  ring

noncomputable def Pp (m : Nat) (A1 A2 E y : ℝ) : ℝ :=
  A1 * pT m (1 / 2) y + A2 * pT m (2 / 3) y + E * y ^ (m + 2)
noncomputable def Pp' (m : Nat) (A1 A2 E y : ℝ) : ℝ :=
  A1 * pTd m (1 / 2) y + A2 * pTd m (2 / 3) y +
    E * (((m + 2 : Nat) : ℝ) * y ^ (m + 1))
noncomputable def Pp'' (m : Nat) (A1 A2 E y : ℝ) : ℝ :=
  A1 * pTdd m (1 / 2) y + A2 * pTdd m (2 / 3) y +
    E * (((m + 2 : Nat) : ℝ) * (((m + 1 : Nat) : ℝ) * y ^ m))

private theorem Pp_hasDerivAt (m : Nat) (A1 A2 E y : ℝ) :
    HasDerivAt (Pp m A1 A2 E) (Pp' m A1 A2 E y) y := by
  unfold Pp Pp'
  exact (((pT_hasDerivAt m (1 / 2) y).const_mul A1).add
    ((pT_hasDerivAt m (2 / 3) y).const_mul A2)).add
      ((hasDerivAt_pow (m + 2) y).const_mul E)

private theorem Pp'_hasDerivAt (m : Nat) (A1 A2 E y : ℝ) :
    HasDerivAt (Pp' m A1 A2 E) (Pp'' m A1 A2 E y) y := by
  unfold Pp' Pp''
  have epsilon : HasDerivAt
      (fun u : ℝ => E * (((m + 2 : Nat) : ℝ) * u ^ (m + 1)))
      (E * (((m + 2 : Nat) : ℝ) * (((m + 1 : Nat) : ℝ) * y ^ m))) y := by
    exact ((hasDerivAt_pow (m + 1) y).const_mul ((m + 2 : Nat) : ℝ)).const_mul E
  exact (((pTd_hasDerivAt m (1 / 2) y).const_mul A1).add
    ((pTd_hasDerivAt m (2 / 3) y).const_mul A2)).add epsilon

private theorem quad_nonneg {c y : ℝ} (hc : 1 / 2 ≤ c) (hy : 20 ≤ y)
    {M : ℝ} (_hM0 : 0 ≤ M) (hM3 : M ≤ 3) :
    0 ≤ c ^ 2 * y ^ 2 - 2 * c * (M + 2) * y + (M + 2) * (M + 1) := by
  have cy : (10 : ℝ) ≤ c * y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (show (0 : ℝ) ≤ y by linarith), hy]
  nlinarith [cy, _hM0, hM3, sq_nonneg (c * y - M - 7)]

private theorem pTdd_nonneg {c : ℝ} (hc : 1 / 2 ≤ c) {m : Nat} (hm : m ≤ 3)
    {y : ℝ} (hy : 20 ≤ y) : 0 ≤ pTdd m c y := by
  unfold pTdd
  apply mul_nonneg _ (Real.exp_pos _).le
  have mNonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have mLe : (m : ℝ) ≤ 3 := by exact_mod_cast hm
  have ym : 0 ≤ y ^ m := pow_nonneg (by linarith) m
  push_cast
  rw [show c ^ 2 * y ^ (m + 2) - 2 * c * ((m : ℝ) + 2) * y ^ (m + 1) +
      ((m : ℝ) + 2) * ((m : ℝ) + 1) * y ^ m =
    y ^ m * (c ^ 2 * y ^ 2 - 2 * c * ((m : ℝ) + 2) * y +
      ((m : ℝ) + 2) * ((m : ℝ) + 1)) by ring]
  apply mul_nonneg ym
  exact quad_nonneg hc hy mNonneg mLe

private theorem Pp_convexOn {A1 A2 E : ℝ} (m : Nat) (hm : m ≤ 3)
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hE : 0 ≤ E) :
    ConvexOn ℝ (Icc 25 26) (Pp m A1 A2 E) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (by unfold Pp pT; fun_prop : Continuous (Pp m A1 A2 E)).continuousOn
  · intro y _
    exact (Pp_hasDerivAt m A1 A2 E y).hasDerivWithinAt
  · intro y _
    exact (Pp'_hasDerivAt m A1 A2 E y).hasDerivWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    unfold Pp''
    have first : 0 ≤ A1 * pTdd m (1 / 2) y :=
      mul_nonneg hA1 (pTdd_nonneg (by norm_num) hm (by linarith [hy.1]))
    have second : 0 ≤ A2 * pTdd m (2 / 3) y :=
      mul_nonneg hA2 (pTdd_nonneg (by norm_num) hm (by linarith [hy.1]))
    have third : 0 ≤ E * (((m + 2 : Nat) : ℝ) * (((m + 1 : Nat) : ℝ) * y ^ m)) := by
      apply mul_nonneg hE
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (pow_nonneg (by linarith [hy.1]) m))
    linarith

def RowHolds (cell : Cell) : Prop :=
  ∀ y ∈ Icc (25 : ℝ) 26, majorant cell.coordinate.column y ≤ cell.target.value

private theorem convex1 : ConvexOn ℝ (Icc 25 26) (majorant 1) := by
  have formula : majorant 1 = G1 certificate.a1.value certificate.a2.value
      certificate.epsilon.value := by
    funext y
    unfold majorant G1 eT
    rw [show -(y / 2) = -((1 / 2 : ℝ) * y) by ring,
      show -(2 * y / 3) = -((2 / 3 : ℝ) * y) by ring]
    ring
  rw [formula]
  exact G1_convexOn (A1 := certificate.a1.value) (A2 := certificate.a2.value)
    (E := certificate.epsilon.value) (by norm_num [certificate, Decimal.value, decimal])
      (by norm_num [certificate, Decimal.value, decimal])

private theorem convexSucc (m : Nat) (hm : m ≤ 3) :
    ConvexOn ℝ (Icc 25 26) (majorant (m + 2)) := by
  have formula : majorant (m + 2) = Pp m certificate.a1.value certificate.a2.value
      certificate.epsilon.value := by
    funext y
    unfold majorant Pp pT
    rw [show -(y / 2) = -((1 / 2 : ℝ) * y) by ring,
      show -(2 * y / 3) = -((2 / 3 : ℝ) * y) by ring]
    ring
  rw [formula]
  exact Pp_convexOn (A1 := certificate.a1.value) (A2 := certificate.a2.value)
    (E := certificate.epsilon.value) m hm
      (by norm_num [certificate, Decimal.value, decimal])
      (by norm_num [certificate, Decimal.value, decimal])
      (by norm_num [certificate, Decimal.value, decimal])

private theorem cell1Holds : RowHolds certificate.cell1 := by
  intro y hy
  exact (convex1.le_max_of_mem_Icc (by norm_num) (by norm_num) hy).trans
    (by simpa [endpointValue, certificate, sourceCell] using
      endpointUpper certificate.cell1 (by simp [Certificate.cells]))

private theorem cellSuccHolds (m : Nat) (hm : m ≤ 3)
    (cell : Cell) (member : cell ∈ certificate.cells)
    (column : cell.coordinate.column = m + 2) : RowHolds cell := by
  intro y hy
  have convex : ConvexOn ℝ (Icc 25 26) (majorant cell.coordinate.column) := by
    simpa [column] using convexSucc m hm
  exact (convex.le_max_of_mem_Icc (by norm_num) (by norm_num) hy).trans
    (by simpa [endpointValue, certificate] using endpointUpper cell member)

/-- Every coordinate in the authenticated shared row has its corrected source bound. -/
theorem row25Cell (cell : Cell) (member : cell ∈ certificate.cells) : RowHolds cell := by
  simp only [Certificate.cells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact cell1Holds
  · exact cellSuccHolds 0 (by norm_num) _ (by simp [Certificate.cells]) rfl
  · exact cellSuccHolds 1 (by norm_num) _ (by simp [Certificate.cells]) rfl
  · exact cellSuccHolds 2 (by norm_num) _ (by simp [Certificate.cells]) rfl
  · exact cellSuccHolds 3 (by norm_num) _ (by simp [Certificate.cells]) rfl

/-- The exact row-25 tuple copied from the pinned PNT+ `table_10` definition. -/
noncomputable def sourceTable : List (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) :=
  [(25, (decimal 18251 8).value, (decimal 45626 7).value,
    (decimal 11407 5).value, (decimal 28516 4).value,
    (decimal 71291 3).value)]

theorem sourceValues (B : Nat → ℝ)
    (member : ((25 : ℝ), B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    B 1 = certificate.cell1.listed.value ∧
      B 2 = certificate.cell2.listed.value ∧
      B 3 = certificate.cell3.listed.value ∧
      B 4 = certificate.cell4.listed.value ∧
      B 5 = certificate.cell5.listed.value := by
  simpa [sourceTable, certificate, sourceCell] using member

/-- Source-dispatch-shaped bridge for the checked numeric premise. The tuple
membership and `k ∈ Icc 1 5` hypotheses match pinned PNT+'s dispatcher; its
`B_8_exact` reduction remains a localized PNT+ rewrite outside this shard. -/
theorem row25OfMem (B : Nat → ℝ)
    (member : ((25 : ℝ), B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    ∀ k ∈ Finset.Icc 1 5, ∀ y ∈ Set.Icc (25 : ℝ) 26,
      majorant k y ≤ B k * margin.value := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sourceValues B member
  intro k hk
  simp only [Finset.mem_Icc] at hk
  obtain ⟨lower, upper⟩ := hk
  interval_cases k
  · simpa [RowHolds, certificate, sourceCell, corrected, decimalMulValue, h1]
      using row25Cell certificate.cell1 (by simp [Certificate.cells])
  · simpa [RowHolds, certificate, sourceCell, corrected, decimalMulValue, h2]
      using row25Cell certificate.cell2 (by simp [Certificate.cells])
  · simpa [RowHolds, certificate, sourceCell, corrected, decimalMulValue, h3]
      using row25Cell certificate.cell3 (by simp [Certificate.cells])
  · simpa [RowHolds, certificate, sourceCell, corrected, decimalMulValue, h4]
      using row25Cell certificate.cell4 (by simp [Certificate.cells])
  · simpa [RowHolds, certificate, sourceCell, corrected, decimalMulValue, h5]
      using row25Cell certificate.cell5 (by simp [Certificate.cells])

theorem endpointValuesBound :
    List.Forall₂ (fun value cell => value ≤ cell.target.value)
      endpointValues certificate.cells := by
  simp only [endpointValues, Certificate.cells, List.map_cons, List.map_nil]
  exact .cons (endpointUpper certificate.cell1 (by simp [Certificate.cells]))
    (.cons (endpointUpper certificate.cell2 (by simp [Certificate.cells]))
      (.cons (endpointUpper certificate.cell3 (by simp [Certificate.cells]))
        (.cons (endpointUpper certificate.cell4 (by simp [Certificate.cells]))
          (.cons (endpointUpper certificate.cell5 (by simp [Certificate.cells])) .nil))))

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
    (cell : Cell) (index : Nat)
    (found : graph.node? anchor = some instruction)
    (operation : instruction.op = { index := 1 })
    (targetFound : instruction.args[index]? = some target)
    (cellFound : certificate.cells[index]? = some cell)
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
  have values : instruction.args.map valuation = endpointValues := by
    change instruction.args.map valuation = endpointValues at related
    exact related
  obtain ⟨input, inputFound, inputBound⟩ :=
    forall₂_right_get? endpointValuesBound index cell cellFound
  have mappedTarget : (instruction.args.map valuation)[index]? =
      some (valuation target) := by
    simp [targetFound]
  have targetValue : endpointValues[index]? = some (valuation target) := by
    rw [← values]
    exact mappedTarget
  have targetInput : valuation target = input := by
    exact Option.some.inj (targetValue.symm.trans inputFound)
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
                match cellFound : certificate.cells[index]? with
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
            | .all | .empty => none
          else none
        else none
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

/-- The pinned source's historical un-margined row-25/k=5 endpoint is
mathematically false; increasing tactic precision cannot repair it. -/
theorem rejectBareK5 :
    ¬ majorant 5 25 ≤ (71.291 : ℝ) := by
  have lower := expTermsLower 25 (by norm_num)
  have half : (3.7266e-6 : ℝ) < Real.exp (-(25 : ℝ) / 2) := by
    norm_num at lower ⊢
    nlinarith [lower.1]
  have twoThird : (5.7777e-8 : ℝ) < Real.exp (-(2 * 25 : ℝ) / 3) := by
    norm_num at lower ⊢
    nlinarith [lower.2]
  unfold majorant
  norm_num [certificate, Decimal.value, decimal]
  nlinarith [half, twoThird]

end Hex.Interval.Experiment.PntTable10Shard
