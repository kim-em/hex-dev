/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPrimalityMathlib.ProofProbe.Support
namespace HexPrimalityMathlib.ProofProbe
/-! Production certificate reification, with no certificate search or replay. -/
def input : Nat := prime31
def certificate : Hex.Nat.PrimeCert := cert31
prime_reify_probe cert31
end HexPrimalityMathlib.ProofProbe
