import Mathlib.Data.ZMod.Basic
import HexModArith

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

/-- Interpret an executable `ZMod64` residue as a Mathlib `ZMod` class. -/
def toZMod (a : Hex.ZMod64 p) : ZMod p :=
  (a.toNat : ZMod p)

/-- Rebuild an executable `ZMod64` residue from a Mathlib `ZMod` class. -/
def ofZMod (a : ZMod p) : Hex.ZMod64 p :=
  Hex.ZMod64.ofNat p a.val

@[simp]
theorem val_toZMod (a : Hex.ZMod64 p) :
    (toZMod a).val = a.toNat := by
  rw [toZMod, ZMod.val_natCast, Nat.mod_eq_of_lt a.toNat_lt]

@[simp]
theorem ofZMod_toZMod (a : Hex.ZMod64 p) :
    ofZMod (toZMod a) = a := by
  cases a with
  | mk val isLt =>
      apply Hex.ZMod64.ext
      simp [ofZMod, toZMod, Hex.ZMod64.ofNat, Hex.ZMod64.normalize, Nat.mod_eq_of_lt isLt]

@[simp]
theorem toZMod_ofZMod (a : ZMod p) :
    toZMod (ofZMod a) = a := by
  apply ZMod.val_injective p
  simp [ofZMod, toZMod]

@[simp]
theorem ofZMod_zero :
    ofZMod (0 : ZMod p) = 0 := by
  rw [ofZMod, ZMod.val_zero]
  rfl

@[simp]
theorem toZMod_zero :
    toZMod (0 : Hex.ZMod64 p) = 0 := by
  apply ZMod.val_injective p
  rw [val_toZMod, ZMod.val_zero]
  simpa using (Hex.ZMod64.toNat_zero (p := p))

@[simp]
theorem toZMod_one :
    toZMod (1 : Hex.ZMod64 p) = 1 := by
  apply ZMod.val_injective p
  rw [val_toZMod, ZMod.val_one_eq_one_mod]
  simpa using (Hex.ZMod64.toNat_one (p := p))

@[simp]
theorem toZMod_add (a b : Hex.ZMod64 p) :
    toZMod (a + b) = toZMod a + toZMod b := by
  apply ZMod.val_injective p
  rw [ZMod.val_add, val_toZMod, val_toZMod, val_toZMod]
  exact Hex.ZMod64.toNat_add a b

@[simp]
theorem toZMod_mul (a b : Hex.ZMod64 p) :
    toZMod (a * b) = toZMod a * toZMod b := by
  apply ZMod.val_injective p
  rw [ZMod.val_mul, val_toZMod, val_toZMod, val_toZMod]
  exact Hex.ZMod64.toNat_mul a b

/-- The executable `ZMod64` representation is ring-equivalent to Mathlib's `ZMod`. -/
def equiv : Hex.ZMod64 p ≃+* ZMod p where
  toFun := toZMod
  invFun := ofZMod
  left_inv := ofZMod_toZMod
  right_inv := toZMod_ofZMod
  map_mul' := toZMod_mul
  map_add' := toZMod_add

@[simp]
theorem equiv_apply (a : Hex.ZMod64 p) :
    equiv a = toZMod a := by
  rfl

@[simp]
theorem equiv_symm_apply (a : ZMod p) :
    equiv.symm a = ofZMod a := by
  rfl

end ZMod64

end HexModArithMathlib
