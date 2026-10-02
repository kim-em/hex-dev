/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDet.Basic
public import HexDet.Int
public import HexDet.Field
public import HexDet.Poly
public import HexDet.MvPoly

public section

/-!
The `HexDet` library is the production determinant entry point for square
`Hex.Matrix` values. `Hex.Det.det` interprets a typed recipe rather than adding
a determinant algorithm of its own: it dispatches to the fraction-free Bareiss
elimination of `HexBareiss` and the Samuelson--Berkowitz characteristic
polynomial of `HexCharPoly`, after the mandatory `n ≤ 2` closed forms.

`Hex.Matrix.det`, the Leibniz reference determinant in `HexDeterminant`, is
untouched. The Mathlib companion `HexDetMathlib` proves every shipped arm equal
to it.

This umbrella is the supported way to obtain all concrete carrier recipes.
Importing a single instance module, such as `HexDet.Int`, gives that carrier's
recipe without the others; importing only `HexDet.Basic` deliberately leaves
every carrier on the generic Berkowitz default. A partial import can change the
arm a call selects, never its value.
-/
