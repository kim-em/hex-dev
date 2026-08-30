/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-! Odd small-factor probe at the supported 512-bit input ceiling:
`97 * (2^505 + 1)`. -/

open Hex.PrimalityTactic

use_hex_primality_norm_num

example : ¬ Nat.Prime
    10160604446909624364520940818952867768480456910917673106556136406570399304040109818357670366579606503796352267531946460412610364318428260037531749637423201 := by
  norm_num
