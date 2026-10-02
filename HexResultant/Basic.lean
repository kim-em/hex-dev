/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly
public import HexPoly.PseudoDiv

public section

/-! Compatibility import for the shared fraction-free polynomial kernel.
The implementation and its computational correctness theorems are owned by
`HexPoly.PseudoDiv`; resultant and signed-remainder consumers reuse it. -/
