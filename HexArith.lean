/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.Nat.ModArith
public import HexArith.Nat.Pow
public import HexArith.Nat.Prime
public import HexArith.Barrett.ReduceNat
public import HexArith.Barrett.Reduce
public import HexArith.Barrett.Context
public import HexArith.CrossCheck
public import HexArith.ExtGcd
public import HexArith.Montgomery.Context
public import HexArith.Montgomery.InvNat
public import HexArith.Montgomery.Redc
public import HexArith.Montgomery.RedcNat
public import HexArith.UInt64.Wide

public section

/-!
`HexArith` collects the low-level arithmetic foundations for the project:
wide-word `UInt64` operations, Nat-level modular-arithmetic lemmas, the
extended-GCD implementations, and the mathlib-free modular reduction and
number-theory layers built on top of them.
-/
