/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality

public section

/-! Bounded-search exhaustion through the core term elaborator. -/

/--
error: primality: certificate search for 3317044064679887385961981 exhausted after 35 attempts (seed 3317044064679887385961981, recursive fuel 178; policy maximum 1040 fuel at 512 bits); no total primality decision was attempted
-/
#guard_msgs in
example : Hex.Nat.Prime 3317044064679887385961981 :=
  primality 3317044064679887385961981
