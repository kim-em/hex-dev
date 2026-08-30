/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-! Bounded-search exhaustion through the Mathlib tactic handler. -/

/--
error: primality: certificate search for 3317044064679887385961981 exhausted after 35 attempts (seed 3317044064679887385961981, recursive fuel 178; policy maximum 1040 fuel at 512 bits); no total primality decision was attempted
-/
#guard_msgs in
example : Nat.Prime 3317044064679887385961981 := by primality
