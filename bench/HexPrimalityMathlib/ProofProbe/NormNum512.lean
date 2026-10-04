/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexPrimalityMathlib.ProofProbe.Support

public section
namespace HexPrimalityMathlib.ProofProbe
open Hex.PrimalityTactic
/-! End-to-end opted-in `norm_num` proof at the supported ceiling. -/
use_hex_primality_norm_num
theorem result : Nat.Prime prime512 := by norm_num
#print axioms result
end HexPrimalityMathlib.ProofProbe
