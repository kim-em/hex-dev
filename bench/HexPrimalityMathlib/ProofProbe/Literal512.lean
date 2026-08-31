/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPrimalityMathlib.ProofProbe.Support
namespace HexPrimalityMathlib.ProofProbe
/-! Ceiling numeral and certificate literal, without search or replay. -/
def input : Nat := prime512
def certificate : Hex.Nat.PrimeCert := cert512
end HexPrimalityMathlib.ProofProbe
