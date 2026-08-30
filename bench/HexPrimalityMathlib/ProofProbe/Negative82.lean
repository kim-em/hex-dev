/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-! Adversarial factor-found probe with two balanced 41/42-bit factors. -/

open Hex.PrimalityTactic

use_hex_primality_norm_num

example : ¬ Nat.Prime 3317044064772611591084773 := by norm_num
