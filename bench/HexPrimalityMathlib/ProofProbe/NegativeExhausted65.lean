/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-! Exhaustion immediately above the rho-search bit boundary. -/

open Hex.PrimalityTactic

use_hex_primality_norm_num

/--
error: unsolved goals
⊢ ¬Nat.Prime 18446744073709551617
-/
#guard_msgs in
example : ¬ Nat.Prime 18446744073709551617 := by norm_num
