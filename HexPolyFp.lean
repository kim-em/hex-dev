/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyFp.Basic
import HexPolyFp.Packed
import HexPolyFp.PrimeField
import HexPolyFp.Compose
import HexPolyFp.Enumeration
import HexPolyFp.Frobenius
import HexPolyFp.SquareFree
import HexPolyFp.ModCompose
import HexPolyFp.Quotient
import HexPolyFp.QuotientFrobenius

/-!
`HexPolyFp` specializes the executable dense-polynomial API to
`Hex.ZMod64 p`, exposing `FpPoly p` together with Frobenius-power
computations, square-free decomposition, and modular composition
modulo a monic polynomial.
-/
