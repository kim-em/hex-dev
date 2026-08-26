/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Absolute

@[expose] public section

/-!
# Exact semantics of public interval natural power

This module characterizes the direct cuts selected by every successful checked
natural power and proves the one-way real image theorem. Empty remains empty at
every exponent. Positive odd powers map source cuts directly; positive even
powers map the exact absolute-value hull before applying the strictly monotone
nonnegative power map.
-/

namespace Hex.Interval

@[simp]
theorem toReal_pow (value : Dyadic) (exponent : Nat) :
    toReal (value ^ exponent) = toReal value ^ exponent := by
  rw [toReal, Dyadic.toRat_pow]
  exact map_pow (Rat.castHom ℝ) value.toRat exponent

@[simp]
private theorem toReal_one : toReal (1 : Dyadic) = 1 := by
  have dyadicOne : (1 : Dyadic).toRat = (1 : Rat) :=
    Dyadic.toRat_natCast 1
  simp [toReal, dyadicOne]

/-- A raw interval has a finite nonnegative lower cut. This syntactic property
is the premise needed for strict monotonicity of positive natural power. -/
private def Raw.Nonnegative : Raw → Prop
  | .empty => True
  | .bounds .unbounded _ => False
  | .bounds (.finite value _) _ => 0 ≤ value

private theorem toReal_le {left right : Dyadic} (h : left ≤ right) :
    toReal left ≤ toReal right := by
  exact (Rat.cast_le (K := ℝ)).2 (Dyadic.toRat_le_toRat_iff.2 h)

private theorem nonnegative_absUnchecked (raw : Raw) :
    raw.absUnchecked.Nonnegative := by
  cases raw with
  | empty => simp [Raw.absUnchecked, Raw.Nonnegative]
  | bounds lower upper =>
      cases lower with
      | unbounded =>
          cases upper with
          | unbounded => simp [Raw.absUnchecked, Raw.Nonnegative]
          | finite upper upperStrict =>
              by_cases nonpositive : upper ≤ 0
              · simp only [Raw.absUnchecked, nonpositive, ↓reduceIte,
                  Raw.Nonnegative]
                rw [← Dyadic.toRat_le_toRat_iff] at nonpositive ⊢
                simpa [Dyadic.toRat_neg] using nonpositive
              · simp [Raw.absUnchecked, Raw.Nonnegative, nonpositive]
      | finite lower lowerStrict =>
          cases upper with
          | unbounded =>
              by_cases nonnegative : 0 ≤ lower <;>
                simp [Raw.absUnchecked, Raw.Nonnegative, nonnegative]
          | finite upper upperStrict =>
              by_cases nonnegative : 0 ≤ lower
              · simp [Raw.absUnchecked, Raw.Nonnegative, nonnegative]
              · by_cases nonpositive : upper ≤ 0
                · simp only [Raw.absUnchecked, nonnegative, ↓reduceIte,
                    nonpositive, Raw.Nonnegative]
                  rw [← Dyadic.toRat_le_toRat_iff] at nonpositive ⊢
                  simpa [Dyadic.toRat_neg] using nonpositive
                · simp [Raw.absUnchecked, Raw.Nonnegative, nonnegative,
                    nonpositive]

private theorem contains_powCuts_odd (raw : Raw) {x : ℝ} {exponent : Nat}
    (odd : Odd exponent) (member : raw.Contains x) :
    (raw.powCutsUnchecked exponent).Contains (x ^ exponent) := by
  cases raw with
  | empty => simp [Raw.Contains] at member
  | bounds lower upper =>
      cases lower with
      | unbounded =>
          cases upper with
          | unbounded =>
              simp [Raw.powCutsUnchecked, Raw.Contains, Lower.Contains,
                Upper.Contains]
          | finite upper upperStrict =>
              cases upperStrict <;>
                simpa [Raw.powCutsUnchecked, Raw.Contains, Lower.Contains,
                  Upper.Contains, toReal_pow, odd.pow_le_pow,
                  odd.pow_lt_pow] using member
      | finite lower lowerStrict =>
          cases upper with
          | unbounded =>
              cases lowerStrict <;>
                simpa [Raw.powCutsUnchecked, Raw.Contains, Lower.Contains,
                  Upper.Contains, toReal_pow, odd.pow_le_pow,
                  odd.pow_lt_pow] using member
          | finite upper upperStrict =>
              cases lowerStrict <;> cases upperStrict <;>
                simpa [Raw.powCutsUnchecked, Raw.Contains, Lower.Contains,
                  Upper.Contains, toReal_pow, odd.pow_le_pow,
                  odd.pow_lt_pow] using member

private theorem contains_powCuts_nonnegative (raw : Raw) {x : ℝ}
    {exponent : Nat} (positiveExponent : exponent ≠ 0)
    (nonnegative : raw.Nonnegative) (member : raw.Contains x) :
    (raw.powCutsUnchecked exponent).Contains (x ^ exponent) := by
  cases raw with
  | empty => simp [Raw.Contains] at member
  | bounds lower upper =>
      cases lower with
      | unbounded => simp [Raw.Nonnegative] at nonnegative
      | finite lower lowerStrict =>
          have lowerDyadic : (0 : Dyadic) ≤ lower := by
            simpa [Raw.Nonnegative] using nonnegative
          have lowerNonnegative : 0 ≤ toReal lower := by
            simpa [toReal] using toReal_le lowerDyadic
          rcases member with ⟨lowerMember, upperMember⟩
          have xNonnegative : 0 ≤ x := by
            cases lowerStrict <;>
              simp [Lower.Contains] at lowerMember <;> linarith
          have resultLower :
              (Lower.finite (lower ^ exponent) lowerStrict).Contains
                (x ^ exponent) := by
            cases lowerStrict with
            | false =>
                simp only [Lower.Contains, toReal_pow]
                exact (pow_le_pow_iff_left₀ lowerNonnegative xNonnegative
                  positiveExponent).2 lowerMember
            | true =>
                simp only [Lower.Contains, toReal_pow]
                exact (pow_lt_pow_iff_left₀ lowerNonnegative xNonnegative
                  positiveExponent).2 lowerMember
          cases upper with
          | unbounded =>
              exact ⟨resultLower, by simp [Upper.Contains]⟩
          | finite upper upperStrict =>
              have upperNonnegative : 0 ≤ toReal upper := by
                cases upperStrict <;>
                  simp [Upper.Contains] at upperMember <;> linarith
              have resultUpper :
                  (Upper.finite (upper ^ exponent) upperStrict).Contains
                    (x ^ exponent) := by
                cases upperStrict with
                | false =>
                    simp only [Upper.Contains, toReal_pow]
                    exact (pow_le_pow_iff_left₀ xNonnegative upperNonnegative
                      positiveExponent).2 upperMember
                | true =>
                    simp only [Upper.Contains, toReal_pow]
                    exact (pow_lt_pow_iff_left₀ xNonnegative upperNonnegative
                      positiveExponent).2 upperMember
              exact ⟨resultLower, resultUpper⟩

private theorem contains_powUnchecked (raw : Raw) {x : ℝ}
    (exponent : Nat) (member : raw.Contains x) :
    (raw.powUnchecked exponent).Contains (x ^ exponent) := by
  cases raw with
  | empty => simp [Raw.Contains] at member
  | bounds lower upper =>
      by_cases zero : exponent = 0
      · subst exponent
        norm_num [Raw.powUnchecked, Raw.Contains, Lower.Contains,
          Upper.Contains, toReal_one]
      · by_cases odd : Odd exponent
        · have mapped := contains_powCuts_odd
            (Raw.bounds lower upper) odd member
          simpa [Raw.powUnchecked, zero, Nat.odd_iff.mp odd] using mapped
        · have even : Even exponent := Nat.not_odd_iff_even.mp odd
          have absolute := contains_absUnchecked
            (Raw.bounds lower upper) member
          have mapped := contains_powCuts_nonnegative
            (Raw.bounds lower upper).absUnchecked zero
            (nonnegative_absUnchecked (Raw.bounds lower upper)) absolute
          simpa [Raw.powUnchecked, zero, Nat.not_odd_iff.mp odd,
            even.pow_abs] using mapped

/-- A successful public natural power has exactly its normalized selected raw
cuts. -/
theorem contains_powWithin {endpointLimit : EndpointLimit}
    {workLimits : Arithmetic.PowLimits} {input result : Hex.Interval}
    {exponent : Nat}
    (checked : powWithin endpointLimit workLimits input exponent = .ready result)
    (x : ℝ) :
    result.Contains x ↔ (Raw.powUnchecked input.view exponent).Contains x := by
  simp only [Contains]
  rw [view_powWithin_ready checked, contains_normalize]

/-- Natural power maps every input member into every successful public image. -/
theorem pow_mem_powWithin {endpointLimit : EndpointLimit}
    {workLimits : Arithmetic.PowLimits} {input result : Hex.Interval}
    {exponent : Nat} {x : ℝ}
    (checked : powWithin endpointLimit workLimits input exponent = .ready result)
    (member : input.Contains x) : result.Contains (x ^ exponent) :=
  (contains_powWithin checked (x ^ exponent)).2
    (contains_powUnchecked input.view exponent member)

end Hex.Interval
