/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2.Field.Word
public import HexGF2.Field.Poly
public import HexGF2.Field.WordLaws
public import HexGF2.Field.Roots
public import HexGF2.Field.Grind

/-!
The `GF(2^n)` wrappers for `hex-gf2`.

`HexGF2.Field.Word` holds the single-word `n < 64` case and the packed helpers
both representations share, with its bare algebraic laws in
`HexGF2.Field.WordLaws`. The arbitrary-degree case is layered:
`HexGF2.Field.Poly` is the representation and its arithmetic laws,
`HexGF2.Field.Roots` the root-count and Frobenius development, and
`HexGF2.Field.Grind` the bundled `Lean.Grind` instances built from both.
-/
