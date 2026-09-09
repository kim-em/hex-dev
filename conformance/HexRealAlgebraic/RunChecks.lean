/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealAlgebraic.Checks

/-! Standalone compiled runner for the larger real algebraic fixtures. -/

/-- Execute all larger Mathlib-free conformance cases. -/
def main : IO Unit := Hex.RealAlgebraicChecks.run true
