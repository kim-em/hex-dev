/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampMathlib.Basic

public section

/-!
The `HexBerlekampMathlib` library contains the Mathlib-facing correctness
surface for executable Berlekamp factorization and Rabin irreducibility tests.

It exposes the transfer from `FpPoly p` to `Polynomial (ZMod p)`, the first
irreducibility theorem statements, and the decidability surface needed by
downstream proof layers.
-/
