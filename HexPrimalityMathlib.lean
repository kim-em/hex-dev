/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib.NormNum
import HexPrimalityMathlib.Prime
import HexPrimalityMathlib.Segment

/-!
The `HexPrimalityMathlib` library relates the Mathlib-free primality
surface of `HexPrimality` to Mathlib's `Nat.Prime`: the `prime_iff`
correspondence, `Nat.Prime`-flavoured transports of the checker, decision,
and search theorems, and the segment statements over the committed table
in Mathlib's `Finset` vocabulary. It also extends `primality` to
`Nat.Prime`; ordinary imports retain Mathlib's `norm_num` behavior, while
`use_hex_primality_norm_num` explicitly selects Hex's thresholded policy
for the current module.
-/
