/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZMathlib.Basic
public import HexPolyZMathlib.Discriminant
public import HexPolyZMathlib.Hadamard
public import HexPolyZMathlib.MahlerSeparation
public import HexPolyZMathlib.Mignotte
public import HexPolyZMathlib.RobinsonForm
public import HexPolyZMathlib.Squarefree

public section

/-!
The `HexPolyZMathlib` library identifies executable integer dense polynomials
with Mathlib's `Polynomial ℤ` API.

This library specializes the generic dense-polynomial equivalence to
`Hex.ZPoly`, exposing the concrete conversion functions, the ring equivalence
used by downstream integer-polynomial proof libraries, and the
Mahler-measure/Mignotte-bound theorem surface over `Polynomial ℤ`.
It also hosts the generic discriminant root-product, sharp column-Hadamard,
and Mahler/Vandermonde inequalities shared by the real- and complex-root
companions.
-/
