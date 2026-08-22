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

end HexTruncatedSeriesMathlib
