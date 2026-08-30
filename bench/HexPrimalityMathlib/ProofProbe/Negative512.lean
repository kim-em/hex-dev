/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-! Factor-found probe at the supported 512-bit input ceiling. -/

open Hex.PrimalityTactic

use_hex_primality_norm_num

example : ¬ Nat.Prime
    6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216824503042048 := by
  norm_num
