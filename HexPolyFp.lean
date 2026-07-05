/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp.Field
public import HexPolyFp.Ring
public import HexPolyFp.Degree
public import HexPolyFp.Packed
public import HexPolyFp.PrimeField
public import HexPolyFp.Compose
public import HexPolyFp.Enumeration
public import HexPolyFp.Frobenius
public import HexPolyFp.SquareFree
public import HexPolyFp.ModCompose
public import HexPolyFp.Quotient
public import HexPolyFp.QuotientFrobenius

public section

/-!
`HexPolyFp` specializes the executable dense-polynomial API to
`Hex.ZMod64 p`, exposing `FpPoly p` together with Frobenius-power
computations, square-free decomposition, and modular composition
modulo a monic polynomial.
-/
