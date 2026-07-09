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

end WordMod

end HexModArithMathlib
