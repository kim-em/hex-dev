/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-! One-restart exhaustion on a balanced 512-bit semiprime. -/

open Hex.PrimalityTactic

use_hex_primality_norm_num

/--
error: unsolved goals
⊢ ¬Nat.Prime 13407807926820848549984871491119855788235523322740973763876191939595871090961335127125233828880698995298214970593191507050244061726229325180256249012290513
-/
#guard_msgs in
example : ¬ Nat.Prime
    13407807926820848549984871491119855788235523322740973763876191939595871090961335127125233828880698995298214970593191507050244061726229325180256249012290513 := by
  norm_num
