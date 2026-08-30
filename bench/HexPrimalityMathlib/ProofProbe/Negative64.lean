/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-! Factor-found probe on a balanced 64-bit semiprime. -/

open Hex.PrimalityTactic

use_hex_primality_norm_num

example : ¬ Nat.Prime 18446743979220271189 := by norm_num
