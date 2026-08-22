/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeriesMathlib.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative

public section

/-!
Elementary operation correspondences for truncated series.

The bundled ring homomorphism in `Basic` already exposes the zero, one,
addition, and multiplication correspondences.  This module records the
precision and derivative interfaces used by the Newton correspondences.
-/

namespace HexTruncatedSeriesMathlib

open Hex Hex.TSeries

universe u

variable {R : Type u} {n : Nat}

/-- Truncating Mathlib's constant series gives the executable constant
series. -/
@[simp]
theorem ofPowerSeries_C [CommRing R] (r : R) :
    ofPowerSeries (n := n) (PowerSeries.C r) = C r := by
  apply Hex.TSeries.ext
  intro i hi
  rw [coeff_ofPowerSeries _ i hi, Hex.TSeries.coeff_C r i hi,
    PowerSeries.coeff_C]

/-- Truncating Mathlib's variable gives the executable variable. -/
@[simp]
theorem ofPowerSeries_X [CommRing R] :
    ofPowerSeries (n := n) (PowerSeries.X : PowerSeries R) = X := by
  apply Hex.TSeries.ext
  intro i hi
  rw [coeff_ofPowerSeries _ i hi, Hex.TSeries.coeff_X i hi]
  simp [PowerSeries.coeff_X]

/-- Truncating an already truncated Mathlib series to a smaller precision is
the direct truncation at that precision. -/
@[simp]
theorem truncate_ofPowerSeries [CommRing R] (f : PowerSeries R)
    {m k : Nat} (hkm : k ≤ m) :
    (ofPowerSeries (n := m) f).truncate k hkm =
      ofPowerSeries (n := k) f := by
  apply Hex.TSeries.ext
  intro i hi
  rw [Hex.TSeries.coeff_truncate _ hkm i hi,
    coeff_ofPowerSeries f i (by omega), coeff_ofPowerSeries f i hi]

/-- Executable multiplication by `x^k` is truncation of multiplication by
Mathlib's `X^k`. -/
@[simp]
theorem mulXPow_ofPowerSeries [CommRing R] (f : PowerSeries R) (k : Nat) :
    (ofPowerSeries (n := n) f).mulXPow k =
      ofPowerSeries (n := n) ((PowerSeries.X : PowerSeries R) ^ k * f) := by
  apply Hex.TSeries.ext
  intro i hi
  rw [Hex.TSeries.coeff_mulXPow _ k i hi,
    coeff_ofPowerSeries _ i hi, PowerSeries.coeff_X_pow_mul']
  by_cases hki : k ≤ i
  · rw [if_pos hki, if_pos hki, coeff_ofPowerSeries f (i - k) (by omega)]
  · rw [if_neg hki, if_neg hki]

/-- Coefficients of a truncated derivative agree with Mathlib's formal
derivative wherever both are represented. -/
theorem coeff_deriv_ofPowerSeries [CommRing R] (f : PowerSeries R)
    (i : Nat) (hi : i < n - 1) :
    (deriv (ofPowerSeries (n := n) f)).coeff i =
      PowerSeries.coeff i (PowerSeries.derivative R f) := by
  rw [Hex.TSeries.coeff_deriv _ i hi,
    coeff_ofPowerSeries f (i + 1) (by omega), PowerSeries.coeff_derivative]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- Executable differentiation commutes with truncation, at the precision
lost by differentiation. -/
@[simp]
theorem deriv_ofPowerSeries [CommRing R] (f : PowerSeries R) :
    (ofPowerSeries (n := n) f).deriv =
      ofPowerSeries (n := n - 1) (PowerSeries.derivative R f) := by
  apply Hex.TSeries.ext
  intro i hi
  rw [coeff_ofPowerSeries _ i hi]
  exact coeff_deriv_ofPowerSeries f i hi

end HexTruncatedSeriesMathlib
