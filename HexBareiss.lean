/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBareiss.BorderedMinor
public import HexBareiss.Bareiss

public section

/-!
The `HexBareiss` library exposes the executable fraction-free Bareiss
determinant algorithm over `Int`, together with the bordered-minor support
(`BorderedMinor`) its correctness development relies on. It builds on the
`HexMatrix` dense core and the `HexDeterminant` Leibniz determinant.
-/
