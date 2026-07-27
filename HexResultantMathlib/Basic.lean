/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Data.Complex.Basic
public import HexResultant
public import HexPolyMathlib

public section

/-!
Core definitions for the Mathlib correspondence of executable resultants.

The bivariate specialization is expressed as a finite Mathlib polynomial sum,
so it does not require installing a global ring structure on `DensePoly`.
-/
open scoped BigOperators

namespace Hex.DensePoly

universe u

variable {R : Type u}

/-- Specialize the coefficient variable of a dense bivariate polynomial while
retaining its outer polynomial variable. -/
@[expose]
noncomputable def specialize [CommRing R] [DecidableEq R]
    (f : DensePoly (DensePoly R)) (a : R) : Polynomial R :=
  Finset.sum (Finset.range f.size) fun i =>
    Polynomial.monomial i (eval (f.coeff i) a)

/-- Evaluate a dense bivariate polynomial at `(a, b)`. -/
@[expose]
noncomputable def evalBivariate [CommRing R] [DecidableEq R]
    (f : DensePoly (DensePoly R)) (a b : R) : R :=
  (specialize f a).eval b

end Hex.DensePoly
