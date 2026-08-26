/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFpMathlib.Basic
public import HexPolyFpMathlib.SquareFree

/-!
`HexPolyFpMathlib` relates the executable prime-field polynomial representation
`Hex.FpPoly p` to Mathlib's `Polynomial (ZMod p)`, through the ring equivalence
`fpPolyEquiv`. It is the crossing point between the executable polynomial tower
and Mathlib's own polynomial type, and it is deliberately independent of any
particular consumer: factoring, finite-field construction, and the packed
`GF(2)` correspondence all need it.
-/
