/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Data.ZMod.Basic
public import HexModArith

public section

/-!
Correspondence definitions between `Hex.ZMod64` and Mathlib's `ZMod`.

This module exposes the concrete conversions between executable machine-word
residues and Mathlib's canonical quotient ring, together with the ring
equivalence and the immediate simp lemmas used by downstream Mathlib-side
libraries.
-/

namespace HexModArithMathlib

open Hex

namespace ZMod64

variable {p : Nat} [Hex.ZMod64.Bounds p]

instance : NeZero p := ⟨Nat.ne_of_gt (Hex.ZMod64.Bounds.pPos (p := p))⟩

/-- Interpret an executable {name}`Hex.ZMod64` residue as a Mathlib
{name}`ZMod` class. -/
@[expose]
def toZMod (a : Hex.ZMod64 p) : ZMod p :=
  (a.toNat : ZMod p)

/-- Rebuild an executable {name}`Hex.ZMod64` residue from a Mathlib
{name}`ZMod` class. -/
@[expose]
def ofZMod (a : ZMod p) : Hex.ZMod64 p :=
  Hex.ZMod64.ofNat p a.val

/-- The canonical representative of a transferred class is the executable residue's
`Nat` value: `(toZMod a).val = a.toNat`. Callers reading the Mathlib-side `val` of a
transferred element recover the machine residue without unfolding the conversion. -/
@[simp, grind =]
theorem val_toZMod (a : Hex.ZMod64 p) :
    (toZMod a).val = a.toNat := by
  rw [toZMod, ZMod.val_natCast, Nat.mod_eq_of_lt a.toNat_lt]

/-- Round-trip {name}`Hex.ZMod64` → {name}`ZMod` →
{name}`Hex.ZMod64` is the identity. This is the left-inverse law making
{name}`HexModArithMathlib.ZMod64.toZMod` injective; a caller that transfers a
residue to Mathlib and back recovers it unchanged. -/
@[simp, grind =]
theorem ofZMod_toZMod (a : Hex.ZMod64 p) :
    ofZMod (toZMod a) = a := by
  cases a with
  | mk val isLt =>
      apply Hex.ZMod64.ext
      simp [ofZMod, toZMod, Hex.ZMod64.ofNat, Hex.ZMod64.normalize, Nat.mod_eq_of_lt isLt]

/-- Round-trip {name}`ZMod` → {name}`Hex.ZMod64` →
{name}`ZMod` is the identity. Together with
{name}`HexModArithMathlib.ZMod64.ofZMod_toZMod`, this shows the two conversions
are mutually inverse and define a ring equivalence. -/
@[simp, grind =]
theorem toZMod_ofZMod (a : ZMod p) :
    toZMod (ofZMod a) = a := by
  apply ZMod.val_injective p
  simp [ofZMod, toZMod]

/-- {name}`ofZMod` carries Mathlib's `0` to the executable `0`, so transferring the additive
identity in from `ZMod` lands on `ZMod64`'s identity. -/
@[simp, grind =]
theorem ofZMod_zero :
    ofZMod (0 : ZMod p) = 0 := by
  rw [ofZMod, ZMod.val_zero]
  rfl

/-- {name}`toZMod` carries the executable `0` to Mathlib's `0`, so the additive identity
transfers out to `ZMod`'s identity. -/
@[simp, grind =]
theorem toZMod_zero :
    toZMod (0 : Hex.ZMod64 p) = 0 := by
  apply ZMod.val_injective p
  rw [val_toZMod, ZMod.val_zero]
  exact Hex.ZMod64.toNat_zero (p := p)

/-- {name}`toZMod` carries the executable `1` to Mathlib's `1`, so the multiplicative
identity transfers out to `ZMod`'s identity. -/
@[simp, grind =]
theorem toZMod_one :
    toZMod (1 : Hex.ZMod64 p) = 1 := by
  apply ZMod.val_injective p
  rw [val_toZMod, ZMod.val_one_eq_one_mod]
  exact Hex.ZMod64.toNat_one (p := p)

/-- {name}`ofZMod` carries Mathlib's `1` to the executable `1`, so the multiplicative
identity transfers in from `ZMod` to `ZMod64`. -/
@[simp, grind =]
theorem ofZMod_one :
    ofZMod (1 : ZMod p) = 1 := by
  rw [← toZMod_one]
  exact ofZMod_toZMod 1

/-- {name}`HexModArithMathlib.ZMod64.toZMod` is additive, so callers can push
the conversion through a sum and transfer additive
{name}`ZMod` identities back to {name}`Hex.ZMod64`. -/
@[simp, grind =]
theorem toZMod_add (a b : Hex.ZMod64 p) :
    toZMod (a + b) = toZMod a + toZMod b := by
  apply ZMod.val_injective p
  rw [ZMod.val_add, val_toZMod, val_toZMod, val_toZMod]
  exact Hex.ZMod64.toNat_add a b

/-- {name}`toZMod` commutes with negation, so additive inverses transfer out to `ZMod`. -/
@[simp, grind =]
theorem toZMod_neg (a : Hex.ZMod64 p) :
    toZMod (-a) = -toZMod a := by
  change (((Hex.ZMod64.neg a).toNat : Nat) : ZMod p) = -((a.toNat : Nat) : ZMod p)
  rw [Hex.ZMod64.toNat_neg]
  have ha : a.toNat ≤ p := Nat.le_of_lt a.toNat_lt
  calc
    (((p - a.toNat) % p : Nat) : ZMod p) = ((p - a.toNat : Nat) : ZMod p) := by
      simp
    _ = ((p : Nat) : ZMod p) - ((a.toNat : Nat) : ZMod p) := by
      rw [Nat.cast_sub ha]
    _ = -((a.toNat : Nat) : ZMod p) := by
      simp

/-- {name}`toZMod` commutes with subtraction, so differences transfer out to `ZMod`. -/
@[simp, grind =]
theorem toZMod_sub (a b : Hex.ZMod64 p) :
    toZMod (a - b) = toZMod a - toZMod b := by
  change (((Hex.ZMod64.sub a b).toNat : Nat) : ZMod p) =
    ((a.toNat : Nat) : ZMod p) - ((b.toNat : Nat) : ZMod p)
  rw [Hex.ZMod64.toNat_sub]
  have hb : b.toNat ≤ p := Nat.le_of_lt b.toNat_lt
  calc
    (((a.toNat + (p - b.toNat)) % p : Nat) : ZMod p) =
        ((a.toNat + (p - b.toNat) : Nat) : ZMod p) := by
      simp
    _ = ((a.toNat : Nat) : ZMod p) + ((p - b.toNat : Nat) : ZMod p) := by
      rw [Nat.cast_add]
    _ = ((a.toNat : Nat) : ZMod p) + (((p : Nat) : ZMod p) - ((b.toNat : Nat) : ZMod p)) := by
      rw [Nat.cast_sub hb]
    _ = ((a.toNat : Nat) : ZMod p) + -((b.toNat : Nat) : ZMod p) := by
      simp
    _ = ((a.toNat : Nat) : ZMod p) - ((b.toNat : Nat) : ZMod p) := by
      exact
        (sub_eq_add_neg (((a.toNat : Nat) : ZMod p))
          (((b.toNat : Nat) : ZMod p))).symm

/-- {name}`HexModArithMathlib.ZMod64.toZMod` is multiplicative, so callers can
push the conversion through a product and transfer multiplicative
{name}`ZMod` identities back to {name}`Hex.ZMod64`. -/
@[simp, grind =]
theorem toZMod_mul (a b : Hex.ZMod64 p) :
    toZMod (a * b) = toZMod a * toZMod b := by
  apply ZMod.val_injective p
  rw [ZMod.val_mul, val_toZMod, val_toZMod, val_toZMod]
  exact Hex.ZMod64.toNat_mul a b

/-- {name}`toZMod` commutes with the `Nat` cast: a numeral built in `ZMod64` transfers to the
same numeral in `ZMod`. Lets callers move `Nat`-literal coefficients across the correspondence. -/
@[simp, grind =]
theorem toZMod_natCast (n : Nat) :
    toZMod ((n : Hex.ZMod64 p)) = (n : ZMod p) := by
  change (((Hex.ZMod64.natCast p n).toNat : Nat) : ZMod p) = (n : ZMod p)
  rw [Hex.ZMod64.toNat_natCast]
  simp

/-- {name}`toZMod` commutes with the `Int` cast: an integer built in `ZMod64` transfers to the
same integer in `ZMod`. Lets callers move signed integer coefficients across the correspondence. -/
@[simp, grind =]
theorem toZMod_intCast (z : Int) :
    toZMod ((z : Hex.ZMod64 p)) = (z : ZMod p) := by
  cases z with
  | ofNat n =>
      change toZMod (Hex.ZMod64.intCast p (Int.ofNat n)) = ((Int.ofNat n : Int) : ZMod p)
      rw [Hex.ZMod64.intCast_ofNat]
      calc
        toZMod (Hex.ZMod64.natCast p n) = (n : ZMod p) := toZMod_natCast (p := p) n
        _ = ((Int.ofNat n : Int) : ZMod p) := by simp
  | negSucc n =>
      change toZMod (Hex.ZMod64.intCast p (Int.negSucc n)) =
        ((Int.negSucc n : Int) : ZMod p)
      rw [Hex.ZMod64.intCast_negSucc]
      change toZMod (-(Hex.ZMod64.natCast p (n + 1))) =
        ((Int.negSucc n : Int) : ZMod p)
      rw [toZMod_neg]
      have hcast :
          toZMod (Hex.ZMod64.natCast p (n + 1)) = (((n + 1 : Nat) : ZMod p)) :=
        toZMod_natCast (p := p) (n + 1)
      calc
        -toZMod (Hex.ZMod64.natCast p (n + 1)) = -(((n + 1 : Nat) : ZMod p)) := by
          exact congrArg Neg.neg hcast
        _ = ((Int.negSucc n : Int) : ZMod p) := by
          exact (Int.cast_negSucc n).symm

/-- {name}`toZMod` commutes with `Nat` powers, so exponentiation transfers out to `ZMod`. -/
@[simp, grind =]
theorem toZMod_pow (a : Hex.ZMod64 p) (n : Nat) :
    toZMod (a ^ n) = toZMod a ^ n := by
  change (((Hex.ZMod64.pow a n).toNat : Nat) : ZMod p) = ((a.toNat : Nat) : ZMod p) ^ n
  rw [Hex.ZMod64.toNat_pow]
  calc
    (((a.toNat ^ n % p : Nat) : ZMod p)) = ((a.toNat ^ n : Nat) : ZMod p) := by
      simp
    _ = ((a.toNat : Nat) : ZMod p) ^ n := by
      rw [Nat.cast_pow]

/-- The executable {name}`Hex.ZMod64` representation is ring-equivalent to
Mathlib's {name}`ZMod`. -/
@[expose]
def equiv : Hex.ZMod64 p ≃+* ZMod p where
  toFun := toZMod
  invFun := ofZMod
  left_inv := ofZMod_toZMod
  right_inv := toZMod_ofZMod
  map_mul' := toZMod_mul
  map_add' := toZMod_add

/-- {name}`equiv` acts as {name}`toZMod` on elements. Rewrites the bundled ring equivalence to the
bare conversion, so the transport `@[simp]` lemmas above fire on {name}`equiv` applications. -/
@[simp, grind =]
theorem equiv_apply (a : Hex.ZMod64 p) :
    equiv a = toZMod a := by
  rfl

/-- `equiv.symm` acts as {name}`ofZMod` on elements. Rewrites the inverse ring equivalence to
the bare conversion, so the transport `@[simp]` lemmas above fire on `equiv.symm`
applications. -/
@[simp, grind =]
theorem equiv_symm_apply (a : ZMod p) :
    equiv.symm a = ofZMod a := by
  rfl

end ZMod64

end HexModArithMathlib
