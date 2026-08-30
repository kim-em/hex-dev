/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-! Factor-found probe at the first certificate-tier bit width. -/

open Hex.PrimalityTactic

use_hex_primality_norm_num

example : ¬ Nat.Prime 16777217 := by norm_num
