/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Std

public section

namespace Hex.Int

/-- Integer sign using comparisons with zero. Compiled comparisons inspect the
integer's sign and size without copying its multiprecision magnitude. -/
@[expose] def signImpl (z : Int) : Int :=
  if z < 0 then -1 else if z = 0 then 0 else 1

/-- The comparison implementation preserves the integer sign at every input. -/
theorem signImpl_eq : signImpl = Int.sign := by
  funext z
  unfold signImpl
  split
  next h => exact (Int.sign_eq_neg_one_of_neg h).symm
  next h =>
    split
    next hzero => subst z; rfl
    next hzero => exact (Int.sign_eq_one_of_pos (by omega)).symm

/-- Compile integer sign through zero comparisons. In the current toolchain,
the constructor-based implementation copies positive multiprecision integers
when it converts their magnitude to a natural number. -/
@[csimp] theorem sign_eq_signImpl : @Int.sign = @signImpl := signImpl_eq.symm

end Hex.Int
