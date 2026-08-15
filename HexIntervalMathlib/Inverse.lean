/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Interval
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

/-!
# Real semantics of public reciprocal enclosure

The runtime operation computes a connected outward enclosure.  Finite lower
cuts use Core's downward `Dyadic.invAtPrec`; finite upper cuts use the same
primitive at the negated input and negate its result.  Across zero the public
operation describes the connected hull of Lean's total inverse, not the exact
generally-disconnected image.
-/

namespace Hex.Interval

@[simp]
theorem toReal_zero : toReal 0 = 0 := by simp [toReal]

/-- Core's precision-indexed reciprocal, interpreted in `ℝ`, rounds toward
negative infinity. -/
theorem roundedDown_le_inv (value : Dyadic) (precision : Precision) :
    toReal (value.invAtPrec precision) ≤ (toReal value)⁻¹ := by
  cases value with
  | zero => simp [toReal, Dyadic.invAtPrec]
  | ofOdd numerator exponent odd =>
      simp only [Dyadic.invAtPrec, toReal]
      exact_mod_cast Rat.toRat_toDyadic_le

/-- Negating a downward-rounded reciprocal of the negated input rounds the
original reciprocal toward positive infinity. -/
theorem inv_le_roundedUp (value : Dyadic) (precision : Precision) :
    (toReal value)⁻¹ ≤ toReal (-(-value).invAtPrec precision) := by
  have rounded := roundedDown_le_inv (-value) precision
  rw [toReal_neg, inv_neg] at rounded
  simpa using neg_le_neg rounded

/-- Exact membership predicate of the computed raw reciprocal cuts.  This is
the cut characterization, deliberately distinct from exact image equality. -/
def Raw.InvContains (precision : Precision) (raw : Raw) (x : ℝ) : Prop :=
  (raw.invUnchecked precision).Contains x

private theorem positive_of_lower (lower : Lower) {x : ℝ}
    (shape : Raw.strictlyPositive lower = true) (member : lower.Contains x) :
    0 < x := by
  cases lower with
  | unbounded => simp [Raw.strictlyPositive] at shape
  | finite value strict =>
      by_cases valuePositiveDyadic : 0 < value
      · have valuePositive : 0 < toReal value := by
          simpa only [toReal_zero] using toReal_lt valuePositiveDyadic
        cases strict <;> simp [Lower.Contains] at member <;> linarith
      · by_cases valueZero : value = 0
        · subst value
          cases strict
          · simp [Raw.strictlyPositive, valuePositiveDyadic] at shape
          · simpa [Lower.Contains] using member
        · simp [Raw.strictlyPositive, valuePositiveDyadic, valueZero] at shape

private theorem negative_of_upper (upper : Upper) {x : ℝ}
    (shape : Raw.strictlyNegative upper = true) (member : upper.Contains x) :
    x < 0 := by
  cases upper with
  | unbounded => simp [Raw.strictlyNegative] at shape
  | finite value strict =>
      by_cases valueNegativeDyadic : value < 0
      · have valueNegative : toReal value < 0 := by
          simpa only [toReal_zero] using toReal_lt valueNegativeDyadic
        cases strict <;> simp [Upper.Contains] at member <;> linarith
      · by_cases valueZero : value = 0
        · subst value
          cases strict
          · simp [Raw.strictlyNegative, valueNegativeDyadic] at shape
          · simpa [Upper.Contains] using member
        · simp [Raw.strictlyNegative, valueNegativeDyadic, valueZero] at shape

private theorem invLower_positive (precision : Precision) (upper : Upper) {x : ℝ}
    (positive : 0 < x) (member : upper.Contains x) :
    (Raw.invLowerUnchecked precision upper).Contains x⁻¹ := by
  cases upper with
  | unbounded => simpa [Raw.invLowerUnchecked, Lower.Contains] using inv_pos.2 positive
  | finite value strict =>
      have valuePositive : 0 < toReal value := by
        cases strict <;> simp [Upper.Contains] at member <;> linarith
      have valueNonzero : value ≠ 0 := by
        intro equal
        subst value
        simp [toReal] at valuePositive
      simp only [Raw.invLowerUnchecked, valueNonzero, if_false, Lower.Contains]
      exact (roundedDown_le_inv value precision).trans
        ((inv_le_inv₀ valuePositive positive).2
          (by cases strict <;> simp [Upper.Contains] at member ⊢ <;> linarith))

private theorem invLower_negative (precision : Precision) (upper : Upper) {x : ℝ}
    (shape : Raw.strictlyNegative upper = true) (negative : x < 0)
    (member : upper.Contains x) :
    (Raw.invLowerUnchecked precision upper).Contains x⁻¹ := by
  cases upper with
  | unbounded => simp [Raw.strictlyNegative] at shape
  | finite value strict =>
      by_cases valueZero : value = 0
      · simp [Raw.invLowerUnchecked, valueZero, Lower.Contains]
      · have valueNegativeDyadic : value < 0 := by
          simp [Raw.strictlyNegative, valueZero] at shape
          exact shape
        have valueNegative : toReal value < 0 := by
          simpa only [toReal_zero] using toReal_lt valueNegativeDyadic
        simp only [Raw.invLowerUnchecked, valueZero, if_false, Lower.Contains]
        exact (roundedDown_le_inv value precision).trans
          ((inv_le_inv_of_neg valueNegative negative).2
            (by cases strict
                · exact member
                · exact le_of_lt member))

private theorem invUpper_positive (precision : Precision) (lower : Lower) {x : ℝ}
    (shape : Raw.strictlyPositive lower = true) (positive : 0 < x)
    (member : lower.Contains x) :
    (Raw.invUpperUnchecked precision lower).Contains x⁻¹ := by
  cases lower with
  | unbounded => simp [Raw.strictlyPositive] at shape
  | finite value strict =>
      by_cases valueZero : value = 0
      · simp [Raw.invUpperUnchecked, valueZero, Upper.Contains]
      · have valuePositive : 0 < toReal value := by
          have valuePositiveDyadic : 0 < value := by
            simp [Raw.strictlyPositive, valueZero] at shape
            exact shape
          simpa only [toReal_zero] using toReal_lt valuePositiveDyadic
        simp only [Raw.invUpperUnchecked, valueZero, if_false, Upper.Contains]
        exact ((inv_le_inv₀ positive valuePositive).2
            (by cases strict
                · exact member
                · exact le_of_lt member)).trans
          (inv_le_roundedUp value precision)

private theorem invUpper_negative (precision : Precision) (lower : Lower) {x : ℝ}
    (negative : x < 0) (member : lower.Contains x) :
    (Raw.invUpperUnchecked precision lower).Contains x⁻¹ := by
  cases lower with
  | unbounded => simpa [Raw.invUpperUnchecked, Upper.Contains] using inv_neg''.mpr negative
  | finite value strict =>
      have valueNegative : toReal value < 0 := by
        cases strict <;> simp [Lower.Contains] at member <;> linarith
      have valueNonzero : value ≠ 0 := by
        intro equal
        subst value
        simp [toReal] at valueNegative
      simp only [Raw.invUpperUnchecked, valueNonzero, if_false, Upper.Contains]
      exact ((inv_le_inv_of_neg negative valueNegative).2
          (by cases strict
              · exact member
              · exact le_of_lt member)).trans
        (inv_le_roundedUp value precision)

private theorem rawContains_inv (precision : Precision) (raw : Raw) {x : ℝ}
    (member : raw.Contains x) : (raw.invUnchecked precision).Contains x⁻¹ := by
  cases raw with
  | empty => simp [Raw.Contains] at member
  | bounds lower upper =>
      rcases member with ⟨lowerMember, upperMember⟩
      by_cases positiveShape : Raw.strictlyPositive lower = true
      · have positive := positive_of_lower lower positiveShape lowerMember
        simpa [Raw.invUnchecked, positiveShape, Raw.Contains] using
          And.intro (invLower_positive precision upper positive upperMember)
            (invUpper_positive precision lower positiveShape positive lowerMember)
      · by_cases negativeShape : Raw.strictlyNegative upper = true
        · have negative := negative_of_upper upper negativeShape upperMember
          simpa [Raw.invUnchecked, positiveShape, negativeShape, Raw.Contains] using
            And.intro
              (invLower_negative precision upper negativeShape negative upperMember)
              (invUpper_negative precision lower negative lowerMember)
        · simp only [Raw.invUnchecked, positiveShape, negativeShape, Bool.false_or]
          by_cases lowerZero : Raw.closedZeroLower lower = true
          · by_cases upperZero : Raw.closedZeroUpper upper = true
            · simp [lowerZero, upperZero, Raw.Contains, Lower.Contains, Upper.Contains]
                at lowerMember upperMember ⊢
              cases lower <;> cases upper <;> simp_all [Raw.closedZeroLower,
                Raw.closedZeroUpper]
            · simp [lowerZero, upperZero, Raw.Contains, Lower.Contains, Upper.Contains]
                at lowerMember upperMember ⊢
              have nonnegative : 0 ≤ x := by
                cases lower with
                | unbounded => simp [Raw.closedZeroLower] at lowerZero
                | finite value strict =>
                    simp [Raw.closedZeroLower] at lowerZero
                    rcases lowerZero with ⟨rfl, rfl⟩
                    simpa [Lower.Contains] using lowerMember
              simpa using inv_nonneg.2 nonnegative
          · by_cases upperZero : Raw.closedZeroUpper upper = true
            · simp [lowerZero, upperZero, Raw.Contains, Lower.Contains, Upper.Contains]
                at lowerMember upperMember ⊢
              have nonpositive : x ≤ 0 := by
                cases upper with
                | unbounded => simp [Raw.closedZeroUpper] at upperZero
                | finite value strict =>
                    simp [Raw.closedZeroUpper] at upperZero
                    rcases upperZero with ⟨rfl, rfl⟩
                    simpa [Upper.Contains] using upperMember
              simpa using inv_nonpos.2 nonpositive
            · simp [lowerZero, upperZero, Raw.Contains, Lower.Contains, Upper.Contains]

/-- A successful reciprocal has exactly its normalized computed outward-cut
predicate. -/
theorem contains_invWithin {limits : Arithmetic.PrecisionLimits}
    {precision : Precision} {input result : Hex.Interval}
    (checked : invWithin limits precision input = .ready result) (x : ℝ) :
    result.Contains x ↔ input.view.InvContains precision x := by
  simp only [Contains, Raw.InvContains]
  rw [view_invWithin_ready checked, contains_normalize]

/-- Every real member of the source maps under Lean's total reciprocal into a
successful public connected outward enclosure. -/
theorem inv_mem_invWithin {limits : Arithmetic.PrecisionLimits}
    {precision : Precision} {input result : Hex.Interval} {x : ℝ}
    (checked : invWithin limits precision input = .ready result)
    (member : input.Contains x) : result.Contains x⁻¹ :=
  (contains_invWithin checked x⁻¹).2 (rawContains_inv precision input.view member)

end Hex.Interval
