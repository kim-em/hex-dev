/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Basic
public import HexRoots.Bisection
public import HexRoots.Cauchy
public import HexRoots.IsolateAll
public import HexRoots.Kantorovich
public import HexRoots.MahlerPrec
public import HexRoots.Newton
public import HexRoots.Pellet
public import HexRoots.Refine
public import HexRoots.SimpleRoot
public import HexRoots.Taylor

public section

/-!
The `HexRoots` library certifies the isolation of the complex roots of
integer-coefficient polynomials. A root isolation is a square in the
complex plane with Gaussian-dyadic centre and power-of-two half-width,
carrying a witness, dischargeable by `decide`, that a certified region
around the square contains exactly one simple root (an *atom*) or exactly
`k` roots counted with multiplicity (a *cluster*). All witness arithmetic
is exact: Gaussian-dyadic Taylor coefficients compared against dyadic
bounds, with no floats and no error budget.

This is the Mathlib-free computational layer; the correctness and
completeness theorems live in the companion `HexRootsMathlib`.
-/
