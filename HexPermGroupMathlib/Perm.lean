/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Cycles
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

/-- The equivalence of `Fin n` given by a forward permutation: `p.get`
one way, `p.inv.get` the other. -/
@[expose] def Perm.toEquiv (p : Perm n) : Fin n ≃ Fin n where
  toFun := p.get
  invFun := p.inv.get
  left_inv := p.inv_get_get
  right_inv := p.get_inv_get

@[simp] theorem Perm.toEquiv_apply (p : Perm n) (i : Fin n) :
    p.toEquiv i = p.get i := rfl

/-- The forward permutation with the same action as an equivalence of
`Fin n`. -/
@[expose] def Perm.ofEquiv (e : Fin n ≃ Fin n) : Perm n :=
  Perm.ofFn e (fun _ _ h => e.injective h)
    (fun i => ⟨e.symm i, e.apply_symm_apply i⟩)

@[simp] theorem Perm.get_ofEquiv (e : Fin n ≃ Fin n) (i : Fin n) :
    (Perm.ofEquiv e).get i = e i :=
  Perm.get_ofFn ..

namespace Perm

@[simp] theorem ofEquiv_toEquiv (p : Perm n) : ofEquiv p.toEquiv = p := by
  ext i
  simp [toEquiv]

@[simp] theorem toEquiv_ofEquiv (e : Equiv.Perm (Fin n)) : (ofEquiv e).toEquiv = e := by
  ext i
  simp [toEquiv]

@[simp] theorem toEquiv_id : (Perm.id n).toEquiv = 1 := by
  ext i
  simp

@[simp] theorem toEquiv_comp (p q : Perm n) :
    (p.comp q).toEquiv = p.toEquiv * q.toEquiv := by
  ext i
  simp [toEquiv]

@[simp] theorem toEquiv_inv (p : Perm n) : p.inv.toEquiv = p.toEquiv⁻¹ := by
  ext i
  simp [toEquiv]

/-- Executable permutations and Mathlib permutations, with the same multiplication
order and left action on the declared domain. -/
@[expose] def equiv : Perm n ≃* Equiv.Perm (Fin n) where
  toFun := toEquiv
  invFun := ofEquiv
  left_inv := ofEquiv_toEquiv
  right_inv := toEquiv_ofEquiv
  map_mul' := toEquiv_comp

@[simp] theorem ofEquiv_one : ofEquiv (1 : Equiv.Perm (Fin n)) = Perm.id n := by
  ext i
  simp

@[simp] theorem ofEquiv_mul (p q : Equiv.Perm (Fin n)) :
    ofEquiv (p * q) = (ofEquiv p).comp (ofEquiv q) := by
  ext i
  simp

@[simp] theorem ofEquiv_inv (p : Equiv.Perm (Fin n)) :
    ofEquiv p⁻¹ = (ofEquiv p).inv := by
  apply equiv.injective
  simp [equiv]

@[simp] theorem toEquiv_pow (p : Perm n) (k : Nat) :
    (p.pow k).toEquiv = p.toEquiv ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ']

end Perm

end Hex
