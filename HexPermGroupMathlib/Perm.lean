/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Cycles
public import HexPermGroupMathlib.Perm.Basic
public import Mathlib.GroupTheory.Perm.Basic

public section

namespace Hex

variable {n : Nat}

/-- Mathlib's group structure uses the computational permutation operations,
including the same left-recursive natural power implementation. -/
instance : Group (Perm n) where
  mul := Perm.comp
  one := Perm.id n
  inv := Perm.inv
  npow k p := p.pow k
  npow_zero _ := rfl
  npow_succ := fun k p => by
    simpa [Perm.pow_def, Perm.mul_def] using Perm.pow_add p k 1
  mul_assoc := Perm.comp_assoc
  one_mul := Perm.id_comp
  mul_one := Perm.comp_id
  inv_mul_cancel := Perm.inv_comp_self

namespace Perm

/-- Executable permutations and Mathlib permutations, with the same multiplication
order and left action on the declared domain. -/
@[expose] def equiv : Perm n ≃* Equiv.Perm (Fin n) where
  toFun := toEquiv
  invFun := ofEquiv
  left_inv := ofEquiv_toEquiv
  right_inv := toEquiv_ofEquiv
  map_mul' := toEquiv_comp

@[simp] theorem toEquiv_pow (p : Perm n) (k : Nat) :
    (p.pow k).toEquiv = p.toEquiv ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ']

end Perm

end Hex
