/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSparsePoly.Basic
public import HexSparsePoly.Arith
public import HexSparsePoly.Dense

public section

/-!
Canonical sparse univariate polynomials: a sorted array of
`(exponent, coefficient)` terms with strictly increasing exponents and no
stored zero coefficients, for inputs whose exponents are large and whose
number of nonzero coefficients is small.
-/
