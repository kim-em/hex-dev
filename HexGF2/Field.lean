/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2.Field.Word
public import HexGF2.Field.Poly

/-!
The `GF(2^n)` wrappers for `hex-gf2`, split by representation:
`HexGF2.Field.Word` for the single-word `n < 64` case and the packed helpers
both share, and `HexGF2.Field.Poly` for the arbitrary-degree case.
-/
