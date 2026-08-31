/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPrimalityMathlib.ProofProbe.Support
namespace HexPrimalityMathlib.ProofProbe
/-! End-to-end bridge proof at the supported ceiling through bare `primality`. -/
theorem result : Nat.Prime prime512 := by primality
#print axioms result
end HexPrimalityMathlib.ProofProbe
