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
# Real semantics of public division enclosure

The supported first slice performs Core's direct rational-backed `divAtPrec`
only for two nonzero finite singleton inputs. Empty and total-zero inputs are
exact; every other nonempty shape uses an explicit whole-line fallback.
-/

namespace Hex.Interval

/-- Core's direct precision-indexed quotient rounds toward negative infinity
when interpreted in `ℝ`, including its total denominator-zero branch. -/
theorem roundedDivDown_le_div (numerator denominator : Dyadic)
    (precision : Precision) :
    toReal (numerator.divAtPrec denominator precision) ≤
      toReal numerator / toReal denominator := by
  cases denominator with
  | zero => simp [toReal, Dyadic.divAtPrec]
  | ofOdd denominator exponent odd =>
      simp only [Dyadic.divAtPrec, toReal]
      exact_mod_cast Rat.toRat_toDyadic_le

/-- Sign reflection turns Core's downward quotient into an upward-rounded
endpoint for the original quotient. -/
theorem div_le_roundedDivUp (numerator denominator : Dyadic)
    (precision : Precision) :
    toReal numerator / toReal denominator ≤
      toReal (-(-numerator).divAtPrec denominator precision) := by
  have rounded := roundedDivDown_le_div (-numerator) denominator precision
  rw [toReal_neg, neg_div] at rounded
  simpa using neg_le_neg rounded

/-- Exact membership predicate of the computed raw division cuts. This is a
cut characterization, not an exact image claim for the whole-line fallback. -/
def Raw.DivContains (precision : Precision) (numerator denominator : Raw)
    (x : ℝ) : Prop :=
  (Raw.divUnchecked precision numerator denominator).Contains x

private theorem eq_bounds_of_singletonValue {raw : Raw} {value : Dyadic}
    (h : raw.singletonValue? = some value) :
    raw = .bounds (.finite value false) (.finite value false) := by
  cases raw with
  | empty => simp [Raw.singletonValue?] at h
  | bounds lower upper =>
      cases lower with
      | unbounded => simp [Raw.singletonValue?] at h
      | finite lower lowerStrict =>
          cases upper with
          | unbounded => simp [Raw.singletonValue?] at h
          | finite upper upperStrict =>
              cases lowerStrict <;> cases upperStrict <;>
                simp [Raw.singletonValue?] at h ⊢
              rcases h with ⟨rfl, rfl⟩
              exact ⟨rfl, rfl⟩

private theorem eq_toReal_of_singletonValue {raw : Raw} {value : Dyadic} {x : ℝ}
    (shape : raw.singletonValue? = some value) (member : raw.Contains x) :
    x = toReal value := by
  rw [eq_bounds_of_singletonValue shape] at member
  simp [Raw.Contains, Lower.Contains, Upper.Contains] at member
  exact le_antisymm member.2 member.1

private theorem rawContains_div (precision : Precision)
    (numerator denominator : Raw) {x y : ℝ}
    (numeratorMember : numerator.Contains x)
    (denominatorMember : denominator.Contains y) :
    (Raw.divUnchecked precision numerator denominator).Contains (x / y) := by
  cases numerator with
  | empty => simp [Raw.Contains] at numeratorMember
  | bounds numeratorLower numeratorUpper =>
      cases denominator with
      | empty => simp [Raw.Contains] at denominatorMember
      | bounds denominatorLower denominatorUpper =>
          let numeratorRaw := Raw.bounds numeratorLower numeratorUpper
          let denominatorRaw := Raw.bounds denominatorLower denominatorUpper
          generalize numeratorShape : numeratorRaw.singletonValue? = numeratorValue
          generalize denominatorShape : denominatorRaw.singletonValue? = denominatorValue
          dsimp only [numeratorRaw, denominatorRaw] at numeratorShape denominatorShape
          cases numeratorValue with
          | none =>
              cases denominatorValue with
              | none =>
                  simp only [Raw.divUnchecked]
                  rw [numeratorShape, denominatorShape]
                  simp [Raw.Contains, Lower.Contains, Upper.Contains]
              | some denominatorValue =>
                  cases denominatorValue with
                  | zero =>
                      have yZero :=
                        eq_toReal_of_singletonValue denominatorShape denominatorMember
                      simp only [Raw.divUnchecked]
                      rw [numeratorShape, denominatorShape]
                      simp [yZero, toReal, Raw.Contains, Lower.Contains, Upper.Contains]
                  | ofOdd denominator exponent odd =>
                      simp only [Raw.divUnchecked]
                      rw [numeratorShape, denominatorShape]
                      simp [Raw.Contains, Lower.Contains, Upper.Contains]
          | some numeratorValue =>
              cases denominatorValue with
              | none =>
                  cases numeratorValue with
                  | zero =>
                      have xZero := eq_toReal_of_singletonValue numeratorShape numeratorMember
                      simp only [Raw.divUnchecked]
                      rw [numeratorShape]
                      simp [xZero, toReal, Raw.Contains, Lower.Contains, Upper.Contains]
                  | ofOdd numerator exponent odd =>
                      simp only [Raw.divUnchecked]
                      rw [numeratorShape, denominatorShape]
                      simp [Raw.Contains, Lower.Contains, Upper.Contains]
              | some denominatorValue =>
                  cases numeratorValue with
                  | zero =>
                      have xZero := eq_toReal_of_singletonValue numeratorShape numeratorMember
                      simp only [Raw.divUnchecked]
                      rw [numeratorShape]
                      simp [xZero, toReal, Raw.Contains, Lower.Contains, Upper.Contains]
                  | ofOdd numerator exponent odd =>
                      cases denominatorValue with
                      | zero =>
                          have yZero :=
                            eq_toReal_of_singletonValue denominatorShape denominatorMember
                          simp only [Raw.divUnchecked]
                          rw [numeratorShape, denominatorShape]
                          simp [yZero, toReal, Raw.Contains, Lower.Contains, Upper.Contains]
                      | ofOdd denominator denominatorExponent denominatorOdd =>
                          have xValue :=
                            eq_toReal_of_singletonValue numeratorShape numeratorMember
                          have yValue :=
                            eq_toReal_of_singletonValue denominatorShape denominatorMember
                          subst x
                          subst y
                          simp only [Raw.divUnchecked]
                          rw [numeratorShape, denominatorShape]
                          simp only [Raw.Contains, Lower.Contains, Upper.Contains]
                          exact ⟨
                            roundedDivDown_le_div
                              (.ofOdd numerator exponent odd)
                              (.ofOdd denominator denominatorExponent denominatorOdd) precision,
                            div_le_roundedDivUp
                              (.ofOdd numerator exponent odd)
                              (.ofOdd denominator denominatorExponent denominatorOdd) precision⟩

/-- A successful public division has exactly its normalized computed-cut
predicate. -/
theorem contains_divWithin {limits : Arithmetic.PrecisionLimits}
    {precision : Precision} {numerator denominator result : Hex.Interval}
    (checked : divWithin limits precision numerator denominator = .ready result)
    (x : ℝ) :
    result.Contains x ↔ numerator.view.DivContains precision denominator.view x := by
  simp only [Contains, Raw.DivContains]
  rw [view_divWithin_ready checked, contains_normalize]

/-- Both source memberships are consumed to show that Lean's total real
division maps into every successful public enclosure. -/
theorem div_mem_divWithin {limits : Arithmetic.PrecisionLimits}
    {precision : Precision} {numerator denominator result : Hex.Interval}
    {x y : ℝ}
    (checked : divWithin limits precision numerator denominator = .ready result)
    (numeratorMember : numerator.Contains x)
    (denominatorMember : denominator.Contains y) :
    result.Contains (x / y) :=
  (contains_divWithin checked (x / y)).2
    (rawContains_div precision numerator.view denominator.view
      numeratorMember denominatorMember)

end Hex.Interval
