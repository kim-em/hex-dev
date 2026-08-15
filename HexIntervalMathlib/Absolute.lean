/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Interval

@[expose] public section

/-!
# Exact semantics of public interval absolute value

This module relates successful resource-checked absolute value to its selected
raw cuts and proves that the result contains the absolute value of every input
member. Sign-separated inputs retain their endpoint strictness; an interval
crossing zero has a closed zero lower cut and selects its upper cut by endpoint
magnitude and attainment.
-/

namespace Hex.Interval

private theorem toReal_le {left right : Dyadic} (h : left ≤ right) :
    toReal left ≤ toReal right := by
  exact (Rat.cast_le (K := ℝ)).2 (Dyadic.toRat_le_toRat_iff.2 h)

private theorem abs_le_right {lower upper x : ℝ}
    (lowerBound : lower ≤ x) (upperBound : x ≤ upper)
    (magnitude : -lower ≤ upper) : |x| ≤ upper := by
  by_cases nonnegative : 0 ≤ x
  · rw [abs_of_nonneg nonnegative]
    exact upperBound
  · rw [abs_of_nonpos (le_of_not_ge nonnegative)]
    linarith

private theorem abs_lt_right {lower upper x : ℝ}
    (lowerBound : lower ≤ x) (upperBound : x < upper)
    (magnitude : -lower < upper) : |x| < upper := by
  by_cases nonnegative : 0 ≤ x
  · rw [abs_of_nonneg nonnegative]
    exact upperBound
  · rw [abs_of_nonpos (le_of_not_ge nonnegative)]
    linarith

private theorem abs_le_left {lower upper x : ℝ}
    (lowerBound : lower ≤ x) (upperBound : x ≤ upper)
    (magnitude : upper ≤ -lower) : |x| ≤ -lower := by
  by_cases nonnegative : 0 ≤ x
  · rw [abs_of_nonneg nonnegative]
    linarith
  · rw [abs_of_nonpos (le_of_not_ge nonnegative)]
    linarith

private theorem abs_lt_left {lower upper x : ℝ}
    (lowerBound : lower < x) (upperBound : x ≤ upper)
    (magnitude : upper < -lower) : |x| < -lower := by
  by_cases nonnegative : 0 ≤ x
  · rw [abs_of_nonneg nonnegative]
    linarith
  · rw [abs_of_nonpos (le_of_not_ge nonnegative)]
    linarith

private theorem abs_lt_tied {lower upper x : ℝ}
    (lowerBound : lower < x) (upperBound : x < upper)
    (magnitude : -lower = upper) : |x| < upper := by
  by_cases nonnegative : 0 ≤ x
  · rw [abs_of_nonneg nonnegative]
    exact upperBound
  · rw [abs_of_nonpos (le_of_not_ge nonnegative)]
    linarith

/-- Raw absolute-value cuts contain the absolute value of every source member. -/
theorem contains_absUnchecked (raw : Raw) {x : ℝ}
    (member : raw.Contains x) : raw.absUnchecked.Contains |x| := by
  cases raw with
  | empty => simp [Raw.Contains] at member
  | bounds lower upper =>
      cases lower with
      | unbounded =>
          cases upper with
          | unbounded =>
              simp [Raw.absUnchecked, Raw.Contains, Lower.Contains,
                Upper.Contains, toReal]
          | finite upper upperStrict =>
              by_cases nonpositive : upper ≤ 0
              · have upperReal : toReal upper ≤ 0 := by
                  simpa [toReal] using toReal_le nonpositive
                have xNonpositive : x ≤ 0 := by
                  cases upperStrict <;>
                    simp [Raw.Contains, Upper.Contains] at member <;> linarith
                have image :
                    (Raw.bounds .unbounded (.finite upper upperStrict)).absUnchecked =
                      (Raw.bounds .unbounded (.finite upper upperStrict)).negUnchecked := by
                  simp [Raw.absUnchecked, Raw.negUnchecked, nonpositive]
                rw [image, abs_of_nonpos xNonpositive,
                  contains_negUnchecked]
                simpa using member
              · simp [Raw.absUnchecked, Raw.Contains, Lower.Contains,
                  Upper.Contains, nonpositive, toReal]
      | finite lower lowerStrict =>
          cases upper with
          | unbounded =>
              by_cases nonnegative : 0 ≤ lower
              · have lowerReal : 0 ≤ toReal lower := by
                  simpa [toReal] using toReal_le nonnegative
                have xNonnegative : 0 ≤ x := by
                  cases lowerStrict <;>
                    simp [Raw.Contains, Lower.Contains] at member <;> linarith
                rw [abs_of_nonneg xNonnegative]
                simpa [Raw.absUnchecked, nonnegative] using member
              · simp [Raw.absUnchecked, Raw.Contains, Lower.Contains,
                  Upper.Contains, nonnegative, toReal]
          | finite upper upperStrict =>
              by_cases nonnegative : 0 ≤ lower
              · have lowerReal : 0 ≤ toReal lower := by
                  simpa [toReal] using toReal_le nonnegative
                have xNonnegative : 0 ≤ x := by
                  cases lowerStrict <;>
                    simp [Raw.Contains, Lower.Contains] at member <;> linarith
                rw [abs_of_nonneg xNonnegative]
                simpa [Raw.absUnchecked, nonnegative] using member
              · by_cases nonpositive : upper ≤ 0
                · have upperReal : toReal upper ≤ 0 := by
                    simpa [toReal] using toReal_le nonpositive
                  have xNonpositive : x ≤ 0 := by
                    cases upperStrict <;>
                      simp [Raw.Contains, Upper.Contains] at member <;> linarith
                  have image :
                      (Raw.bounds (.finite lower lowerStrict)
                          (.finite upper upperStrict)).absUnchecked =
                        (Raw.bounds (.finite lower lowerStrict)
                          (.finite upper upperStrict)).negUnchecked := by
                    simp [Raw.absUnchecked, Raw.negUnchecked, nonnegative,
                      nonpositive]
                  rw [image, abs_of_nonpos xNonpositive,
                    contains_negUnchecked]
                  simpa using member
                · rcases member with ⟨lowerMember, upperMember⟩
                  have lowerWeak : toReal lower ≤ x := by
                    cases lowerStrict with
                    | false => exact lowerMember
                    | true => exact le_of_lt lowerMember
                  have upperWeak : x ≤ toReal upper := by
                    cases upperStrict with
                    | false => exact upperMember
                    | true => exact le_of_lt upperMember
                  by_cases leftSmaller : -lower < upper
                  · have magnitude : -toReal lower < toReal upper := by
                      simpa [toReal_neg] using toReal_lt leftSmaller
                    have upperAbs :
                        (Upper.finite upper upperStrict).Contains |x| := by
                      cases upperStrict with
                      | false =>
                          exact abs_le_right lowerWeak upperWeak (le_of_lt magnitude)
                      | true => exact abs_lt_right lowerWeak upperMember magnitude
                    simpa [Raw.absUnchecked, Raw.Contains, Lower.Contains,
                      nonnegative, nonpositive, leftSmaller, toReal] using
                        And.intro (abs_nonneg x) upperAbs
                  · by_cases tied : -lower = upper
                    · have magnitude : -toReal lower = toReal upper := by
                        simpa [toReal_neg] using congrArg toReal tied
                      have upperAbs :
                          (Upper.finite upper (lowerStrict && upperStrict)).Contains |x| := by
                        cases lowerStrict <;> cases upperStrict
                        · exact abs_le_right lowerWeak upperWeak (le_of_eq magnitude)
                        · exact abs_le_right lowerWeak upperWeak (le_of_eq magnitude)
                        · exact abs_le_right lowerWeak upperWeak (le_of_eq magnitude)
                        · exact abs_lt_tied lowerMember upperMember magnitude
                      have image :
                          (Raw.bounds (.finite lower lowerStrict)
                              (.finite upper upperStrict)).absUnchecked =
                            .bounds (.finite 0 false)
                              (.finite upper (lowerStrict && upperStrict)) := by
                        simp [Raw.absUnchecked, nonnegative, nonpositive, tied]
                      rw [image]
                      exact ⟨by simp [Lower.Contains, toReal],
                        upperAbs⟩
                    · have magnitude : toReal upper < -toReal lower := by
                        have notLess : ¬-toReal lower < toReal upper := by
                          intro h
                          exact leftSmaller (toReal_lt_iff.mp (by simpa [toReal_neg] using h))
                        have notEqual : toReal upper ≠ -toReal lower := by
                          intro h
                          exact tied (toReal_inj.mp (by simpa [toReal_neg] using h.symm))
                        exact lt_of_le_of_ne (le_of_not_gt notLess) notEqual
                      have upperAbs :
                          (Upper.finite (-lower) lowerStrict).Contains |x| := by
                        cases lowerStrict with
                        | false =>
                            simpa [Upper.Contains, toReal_neg] using
                              abs_le_left lowerWeak upperWeak (le_of_lt magnitude)
                        | true =>
                            simpa [Upper.Contains, toReal_neg] using
                              abs_lt_left lowerMember upperWeak magnitude
                      simpa [Raw.absUnchecked, Raw.Contains, Lower.Contains,
                        nonnegative, nonpositive, leftSmaller, tied, toReal,
                        toReal_neg] using And.intro (abs_nonneg x) upperAbs

/-- A successful public absolute value has exactly the normalized selected
raw cuts. -/
theorem contains_absWithin {limit : EndpointLimit}
    {input result : Hex.Interval}
    (checked : absWithin limit input = .ready result) (x : ℝ) :
    result.Contains x ↔ (Raw.absUnchecked input.view).Contains x := by
  simp only [Contains]
  rw [view_absWithin_ready checked, contains_normalize]

/-- Absolute value maps every input member into the successful public image. -/
theorem abs_mem_absWithin {limit : EndpointLimit}
    {input result : Hex.Interval} {x : ℝ}
    (checked : absWithin limit input = .ready result)
    (member : input.Contains x) : result.Contains |x| :=
  (contains_absWithin checked |x|).2 (contains_absUnchecked input.view member)

end Hex.Interval
