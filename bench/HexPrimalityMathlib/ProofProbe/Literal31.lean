/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexPrimalityMathlib.ProofProbe.Support

public section
namespace HexPrimalityMathlib.ProofProbe
/-! Fixed numeral and emitted certificate literal, without search or replay. -/
def input : Nat := prime31
def certificate : Hex.Nat.PrimeCert := cert31
end HexPrimalityMathlib.ProofProbe
