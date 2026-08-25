/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast.Plan
public import HexTruncatedSeries

public section

/-!
Coefficientwise bridges between normalized dense polynomials and fixed-length
truncated series.  Reversal carries an explicit zero-extension guard so Nat
subtraction cannot alias out-of-range positions to the constant coefficient.
-/

namespace Hex.DensePoly

universe u

variable {R : Type u} [Zero R] [DecidableEq R]

/-- Reverse a dense polynomial from its leading end into an exactly `n`-term
truncated series, padding with zeros when `n` exceeds the polynomial size. -/
@[expose]
def reverseSeries (f : DensePoly R) (n : Nat) : TSeries R n :=
  TSeries.ofFn fun i =>
    if i < f.size then f.coeff (f.size - 1 - i) else 0

/-- Coefficient law for zero-extending polynomial reversal. -/
theorem coeff_reverseSeries (f : DensePoly R) (n i : Nat) (hi : i < n) :
    (reverseSeries f n).coeff i =
      if i < f.size then f.coeff (f.size - 1 - i) else 0 := by
  exact TSeries.coeff_ofFn _ i hi

/-- Inside the polynomial support, reversal reads down from the leading
coefficient. -/
theorem coeff_reverseSeries_of_lt (f : DensePoly R) (n i : Nat)
    (hi : i < n) (hf : i < f.size) :
    (reverseSeries f n).coeff i = f.coeff (f.size - 1 - i) := by
  rw [coeff_reverseSeries f n i hi, _root_.ite_eq_left hf]

/-- Outside the polynomial support, reversal is zero rather than the constant
coefficient selected by saturated Nat subtraction. -/
theorem coeff_reverseSeries_of_size_le (f : DensePoly R) (n i : Nat)
    (hi : i < n) (hf : f.size ≤ i) :
    (reverseSeries f n).coeff i = 0 := by
  rw [coeff_reverseSeries f n i hi, _root_.ite_eq_right (Nat.not_lt.mpr hf)]

/-- Convert all represented coefficients of a truncated series to a normalized
dense polynomial. -/
@[expose]
def polyOfSeries {n : Nat} (a : TSeries R n) : DensePoly R :=
  ofList ((List.range n).map a.coeff)

/-- Coefficient law for conversion from a fixed series prefix. -/
theorem coeff_polyOfSeries {n : Nat} (a : TSeries R n) (i : Nat) :
    (polyOfSeries a).coeff i = if i < n then a.coeff i else 0 := by
  unfold polyOfSeries
  rw [coeff_ofList]
  by_cases hi : i < n
  · simp [List.getD, hi]
  · rw [List.getD_eq_getElem?_getD]
    simp [hi]
    rfl

/-- Converting a series to a polynomial and reading a represented coefficient
returns the original coefficient. -/
theorem coeff_polyOfSeries_of_lt {n : Nat} (a : TSeries R n) (i : Nat)
    (hi : i < n) :
    (polyOfSeries a).coeff i = a.coeff i := by
  rw [coeff_polyOfSeries, _root_.ite_eq_left hi]

/-- Converting a reversed polynomial prefix back to a polynomial exposes the
same guarded reversal coefficient law. -/
theorem coeff_polyOf_reverseSeries (f : DensePoly R) (n i : Nat) :
    (polyOfSeries (reverseSeries f n)).coeff i =
      if i < n then
        if i < f.size then f.coeff (f.size - 1 - i) else 0
      else 0 := by
  rw [coeff_polyOfSeries]
  split <;> rename_i h
  · exact coeff_reverseSeries f n i h
  · rfl

end Hex.DensePoly
