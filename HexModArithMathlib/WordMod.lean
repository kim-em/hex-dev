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
Correspondence between the executable `Hex.WordMod` residue ring and Mathlib's
`ZMod`. `toZMod` sends a Montgomery-form residue to its class in `ZMod m.toNat`;
the transport lemmas below (mirroring `HexModArithMathlib.ZMod64`) are the
homomorphism laws used to lift the executable word arithmetic to Mathlib and,
downstream, to prove the word-sized CLD kernel byte-identical to the bignum path
(issue #8691, Phase 2).

`m.toNat` is positive (`ctx.p_pos`) but that fact needs `ctx`, which `m.toNat`
does not mention, so `NeZero m.toNat` cannot be a free instance; each proof
introduces it locally.
-/

namespace HexModArithMathlib

open Hex

namespace WordMod

variable {m : UInt64} {ctx : _root_.MontCtx m}

/-- Interpret an executable `WordMod` residue as a Mathlib `ZMod` class. -/
@[expose]
def toZMod (a : Hex.WordMod ctx) : ZMod m.toNat := (a.toNat : ZMod m.toNat)

/-- The canonical representative of a transferred class is the residue's value. -/
@[simp] theorem val_toZMod (a : Hex.WordMod ctx) : (toZMod a).val = a.toNat := by
  haveI : NeZero m.toNat := ⟨Nat.ne_of_gt ctx.p_pos⟩
  rw [toZMod, ZMod.val_natCast, Nat.mod_eq_of_lt a.toNat_lt]

/-- `toZMod` is injective: its `ZMod` value is the residue, which pins the word. -/
theorem toZMod_injective : Function.Injective (toZMod (ctx := ctx)) := by
  intro a b h
  have hval : a.toNat = b.toNat := by
    have := congrArg ZMod.val h
    rwa [val_toZMod, val_toZMod] at this
  apply Hex.WordMod.ext
  apply UInt64.toNat_inj.mp
  calc a.val.toNat
      = a.toNat * UInt64.word % m.toNat := (Hex.WordMod.toNat_mul_word a).symm
    _ = b.toNat * UInt64.word % m.toNat := by rw [hval]
    _ = b.val.toNat := Hex.WordMod.toNat_mul_word b

@[simp] theorem toZMod_zero : toZMod (0 : Hex.WordMod ctx) = 0 := by
  haveI : NeZero m.toNat := ⟨Nat.ne_of_gt ctx.p_pos⟩
  apply ZMod.val_injective
  rw [val_toZMod, ZMod.val_zero, Hex.WordMod.toNat_zero]

@[simp] theorem toZMod_add (a b : Hex.WordMod ctx) :
    toZMod (a + b) = toZMod a + toZMod b := by
  haveI : NeZero m.toNat := ⟨Nat.ne_of_gt ctx.p_pos⟩
  apply ZMod.val_injective
  rw [ZMod.val_add, val_toZMod, val_toZMod, val_toZMod, Hex.WordMod.toNat_add]

@[simp] theorem toZMod_mul (a b : Hex.WordMod ctx) :
    toZMod (a * b) = toZMod a * toZMod b := by
  haveI : NeZero m.toNat := ⟨Nat.ne_of_gt ctx.p_pos⟩
  apply ZMod.val_injective
  rw [ZMod.val_mul, val_toZMod, val_toZMod, val_toZMod, Hex.WordMod.toNat_mul]

@[simp] theorem toZMod_one : toZMod (1 : Hex.WordMod ctx) = 1 := by
  haveI : NeZero m.toNat := ⟨Nat.ne_of_gt ctx.p_pos⟩
  apply ZMod.val_injective
  rw [val_toZMod, Hex.WordMod.toNat_one, ZMod.val_one_eq_one_mod]

@[simp] theorem toZMod_neg (a : Hex.WordMod ctx) : toZMod (-a) = -toZMod a := by
  have hle : a.toNat ≤ m.toNat := Nat.le_of_lt a.toNat_lt
  rw [toZMod, Hex.WordMod.toNat_neg]
  calc (((m.toNat - a.toNat) % m.toNat : Nat) : ZMod m.toNat)
      = ((m.toNat - a.toNat : Nat) : ZMod m.toNat) := by
        rw [ZMod.natCast_mod]
    _ = ((m.toNat : Nat) : ZMod m.toNat) - ((a.toNat : Nat) : ZMod m.toNat) := by
        rw [Nat.cast_sub hle]
    _ = -toZMod a := by rw [ZMod.natCast_self]; simp [toZMod]

@[simp] theorem toZMod_sub (a b : Hex.WordMod ctx) :
    toZMod (a - b) = toZMod a - toZMod b := by
  have hle : b.toNat ≤ m.toNat := Nat.le_of_lt b.toNat_lt
  rw [toZMod, Hex.WordMod.toNat_sub]
  calc (((a.toNat + (m.toNat - b.toNat)) % m.toNat : Nat) : ZMod m.toNat)
      = ((a.toNat + (m.toNat - b.toNat) : Nat) : ZMod m.toNat) := by
        rw [ZMod.natCast_mod]
    _ = ((a.toNat : Nat) : ZMod m.toNat)
          + (((m.toNat : Nat) : ZMod m.toNat) - ((b.toNat : Nat) : ZMod m.toNat)) := by
        rw [Nat.cast_add, Nat.cast_sub hle]
    _ = toZMod a - toZMod b := by rw [ZMod.natCast_self]; simp [toZMod, sub_eq_add_neg]

/-! ### Mathlib `CommRing` structure, transferred along `toZMod`.

`WordMod` already carries `Zero/One/Add/Mul/Neg/Sub/NatCast`; the remaining data
a `CommRing` needs (`SMul ℕ`, `SMul ℤ`, `Pow ℕ`, `IntCast`) is defined here so
that each transports to `ZMod` immediately, then `Function.Injective.commRing`
pulls the ring structure back through the injective `toZMod`. -/

instance : SMul ℕ (Hex.WordMod ctx) := ⟨fun n a => (n : Hex.WordMod ctx) * a⟩

instance : IntCast (Hex.WordMod ctx) :=
  ⟨fun z => match z with
    | Int.ofNat n => (n : Hex.WordMod ctx)
    | Int.negSucc n => -((n + 1 : Nat) : Hex.WordMod ctx)⟩

instance : SMul ℤ (Hex.WordMod ctx) := ⟨fun z a => (z : Hex.WordMod ctx) * a⟩

instance : Pow (Hex.WordMod ctx) ℕ := ⟨fun a n => npowRec n a⟩

@[simp] theorem toZMod_natCast (n : Nat) :
    toZMod ((n : Hex.WordMod ctx)) = (n : ZMod m.toNat) := by
  haveI : NeZero m.toNat := ⟨Nat.ne_of_gt ctx.p_pos⟩
  show toZMod (Hex.WordMod.ofNat n) = _
  rw [toZMod, Hex.WordMod.toNat_ofNat, ZMod.natCast_mod]

@[simp] theorem toZMod_intCast (z : Int) :
    toZMod ((z : Hex.WordMod ctx)) = (z : ZMod m.toNat) := by
  cases z with
  | ofNat n =>
      show toZMod ((n : Hex.WordMod ctx)) = _
      rw [toZMod_natCast]; simp
  | negSucc n =>
      show toZMod (-((n + 1 : Nat) : Hex.WordMod ctx)) = _
      rw [toZMod_neg, toZMod_natCast]
      exact (Int.cast_negSucc n).symm

theorem toZMod_npowRec (a : Hex.WordMod ctx) (n : Nat) :
    toZMod (npowRec n a) = toZMod a ^ n := by
  induction n with
  | zero => simp [npowRec, toZMod_one]
  | succ k ih => rw [npowRec, toZMod_mul, ih, pow_succ]

/-- The executable `WordMod` residue ring is a Mathlib `CommRing`, pulled back
along the injective `toZMod`. -/
instance : CommRing (Hex.WordMod ctx) :=
  Function.Injective.commRing toZMod toZMod_injective
    toZMod_zero toZMod_one toZMod_add toZMod_mul toZMod_neg toZMod_sub
    (fun n x => by
      show toZMod ((n : Hex.WordMod ctx) * x) = n • toZMod x
      rw [toZMod_mul, toZMod_natCast, nsmul_eq_mul])
    (fun z x => by
      show toZMod ((z : Hex.WordMod ctx) * x) = z • toZMod x
      rw [toZMod_mul, toZMod_intCast, zsmul_eq_mul])
    (fun x n => toZMod_npowRec x n)
    toZMod_natCast toZMod_intCast

/-- `toZMod` packaged as a ring homomorphism. -/
def toZModRingHom : Hex.WordMod ctx →+* ZMod m.toNat where
  toFun := toZMod
  map_one' := toZMod_one
  map_mul' := toZMod_mul
  map_zero' := toZMod_zero
  map_add' := toZMod_add

@[simp] theorem toZModRingHom_apply (a : Hex.WordMod ctx) :
    toZModRingHom a = toZMod a := by
  simp only [toZModRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]

end WordMod

end HexModArithMathlib
