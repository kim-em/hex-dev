/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMinPolyTheory.Basic
public import HexMinPolyTheory.Order
public import HexMinPolyTheory.CharPoly
public import HexMinPolyTheory.Kernel
public import HexMinPolyTheory.Tactic

public section

/-!
Mathlib correspondence for executable matrix minimal polynomials.

This umbrella identifies `Hex.Matrix.minPoly` with Mathlib's `minpoly`,
transports vector-order and LCM contracts, and exposes characteristic-
polynomial bounds plus transpose and similarity invariance.
-/
