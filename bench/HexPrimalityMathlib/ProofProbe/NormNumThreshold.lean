/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPrimalityMathlib.ProofProbe.Support
namespace HexPrimalityMathlib.ProofProbe
open Hex.PrimalityTactic
/-! Opted-in `norm_num` on the first tested prime above the threshold. -/
use_hex_primality_norm_num
theorem result : Nat.Prime 16777259 := by norm_num
#print axioms result
end HexPrimalityMathlib.ProofProbe
