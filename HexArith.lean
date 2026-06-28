/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexArith.Nat.ModArith
import HexArith.Nat.Pow
import HexArith.Nat.Prime
import HexArith.Barrett.ReduceNat
import HexArith.Barrett.Reduce
import HexArith.Barrett.Context
import HexArith.CrossCheck
import HexArith.ExtGcd
import HexArith.Montgomery.Context
import HexArith.Montgomery.InvNat
import HexArith.Montgomery.Redc
import HexArith.Montgomery.RedcNat
import HexArith.UInt64.Wide

/-!
`HexArith` collects the low-level arithmetic foundations for the project:
wide-word `UInt64` operations, Nat-level modular-arithmetic lemmas, the
extended-GCD implementations, and the mathlib-free modular reduction and
number-theory layers built on top of them.
-/
