/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-! Factor-found probe on the adversarial strong pseudoprime
`3215031751 = 151 * 751 * 28351`. -/

open Hex.PrimalityTactic

use_hex_primality_norm_num

example : ¬ Nat.Prime 3215031751 := by norm_num
