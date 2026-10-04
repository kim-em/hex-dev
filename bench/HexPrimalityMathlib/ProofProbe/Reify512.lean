/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexPrimalityMathlib.ProofProbe.Support

public section
namespace HexPrimalityMathlib.ProofProbe
/-! Production certificate reification at the ceiling, without search or replay. -/
def input : Nat := prime512
def certificate : Hex.Nat.PrimeCert := cert512
prime_reify_probe cert512
end HexPrimalityMathlib.ProofProbe
