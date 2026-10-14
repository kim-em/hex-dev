/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPrimalityTheory.ProofProbe.Support
namespace HexPrimalityTheory.ProofProbe
/-! Fixed numeral and emitted certificate literal, without search or replay. -/
def input : Nat := prime31
def certificate : Hex.Nat.PrimeCert := cert31
end HexPrimalityTheory.ProofProbe
