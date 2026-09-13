/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArithMathlib.ZMod64Equiv
public import Mathlib.Algebra.Ring.InjSurj

public section

namespace HexModArithMathlib.ZMod64

variable {p : Nat} [Hex.ZMod64.Bounds p]

/-- Scalar multiplication by naturals transfers to `ZMod`. -/
theorem toZMod_nsmul (n : Nat) (a : Hex.ZMod64 p) :
    toZMod (n • a) = n • toZMod a := by
  rw [Lean.Grind.Semiring.nsmul_eq_natCast_mul, toZMod_mul, toZMod_natCast,
    nsmul_eq_mul]

/-- Scalar multiplication by integers transfers to `ZMod`. -/
theorem toZMod_zsmul (n : Int) (a : Hex.ZMod64 p) :
    toZMod (n • a) = n • toZMod a := by
  cases n with
  | ofNat n => exact (toZMod_nsmul n a).trans (natCast_zsmul (toZMod a) n).symm
  | negSucc n =>
    change toZMod (-( (n + 1) • a)) = _
    rw [toZMod_neg, toZMod_nsmul]
    change -((n + 1) • toZMod a) = (-((n + 1 : Nat) : Int)) • toZMod a
    rw [neg_zsmul, natCast_zsmul]

/-- Mathlib's ring laws transported through `equiv`, retaining every executable
operation, including scalar multiplication, casts, subtraction, and powers.
Scoped to preserve existing exact Grind instance identities on import. -/
scoped instance commRing : CommRing (Hex.ZMod64 p) :=
  equiv.injective.commRing toZMod toZMod_zero toZMod_one toZMod_add toZMod_mul
    toZMod_neg toZMod_sub toZMod_nsmul toZMod_zsmul toZMod_pow
    toZMod_natCast toZMod_intCast

end HexModArithMathlib.ZMod64
