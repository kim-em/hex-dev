/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor
import HexPrimalityTheory

-- Standard imports and only the tested finite caller heartbeat allowance.
-- Power expressions exercise normalization separately from the numeral guards.
-- Warnings from power normalization are left visible.
set_option maxHeartbeats 4000000

#guard_msgs (drop info) in
example : Nat.Prime (2 ^ 256 - 2 ^ 32 - 977) := by primality?

#guard_msgs (drop info) in
example : Nat.Prime (2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1) := by primality?

#guard_msgs (drop info) in
example : Nat.Prime (2 ^ 448 - 2 ^ 224 - 1) := by primality?

-- The stage-2 option also works on Mathlib goals without maxAttempts syntax.
#guard_msgs (drop info) in
example : Nat.Prime 1000003 := by
  primality? (pMinusOneStage2 := true)
