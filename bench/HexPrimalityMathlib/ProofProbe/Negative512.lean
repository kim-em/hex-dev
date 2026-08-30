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
    10055855947456947824680518748654384595609524365444295033292671082791323022555160232601405723625177570767523893639864538140315412108959927459825236754563075 := by
  norm_num
