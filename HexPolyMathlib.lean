/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyMathlib.Basic
public import HexPolyMathlib.Euclid

public section

/-!
The `HexPolyMathlib` library identifies the executable `HexPoly` core with
Mathlib's `Polynomial` API.

This library exposes the concrete conversion functions between
`Hex.DensePoly` and `Polynomial`, together with the ring equivalence and
Euclidean-algorithm correspondence layer used by downstream Mathlib-facing
polynomial libraries.
-/
