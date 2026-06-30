/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqField.Basic
public import HexGFqField.Operations

public section

/-!
Thin finite-field wrapper for executable `F_p[x] / (f)`.

`HexGFqField` reuses the quotient-ring representation from `HexGFqRing`
unchanged: `GFqField.FiniteField` is just a wrapper around reduced residues,
with explicit conversions, quotient-backed arithmetic, exponentiation, and the
Frobenius map `a ↦ a ^ p`.
-/
