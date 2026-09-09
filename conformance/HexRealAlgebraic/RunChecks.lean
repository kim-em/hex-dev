/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealAlgebraic.Checks
import HexNumberField.ComplexChecks

/-! Standalone compiled runner for the larger real algebraic fixtures. -/

/-- Execute all larger Mathlib-free conformance cases. -/
def main (args : List String) : IO Unit := do
  match args with
  | [] =>
    Hex.RealAlgebraicChecks.run true
    Hex.ComplexAlgebraicChecks.run
  | ["--complex"] => Hex.ComplexAlgebraicChecks.run
  | _ => throw (IO.userError "usage: hexrealalgebraic_conformance [--complex]")
