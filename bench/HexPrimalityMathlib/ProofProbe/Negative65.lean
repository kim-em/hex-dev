/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-! Odd factor-found probe immediately above 64 bits:
`2^64 + 1 = 274177 * 67280421310721`. -/

open Hex.PrimalityTactic

use_hex_primality_norm_num

example : ¬ Nat.Prime 18446744073709551617 := by norm_num
