/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Order
public import HexPermGroupMathlib.Word
public import Mathlib.Data.Finite.Perm
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace Hex.PermGroup

/-- Convert generated Hex permutations to Mathlib's closure, without changing
which elements are counted. -/
noncomputable def generatedEquiv (S : Array (Perm n)) :
    {p : Perm n // Generated S p} ≃ closure S where
  toFun p := ⟨p.val.toEquiv, generated_iff_mem.mp p.property⟩
  invFun p := ⟨Perm.ofEquiv p.val, generated_iff_mem.mpr (by simp [p.property])⟩
  left_inv p := Subtype.ext (Perm.ofEquiv_toEquiv p.val)
  right_inv p := Subtype.ext (Perm.toEquiv_ofEquiv p.val)

/-- The Mathlib-free order predicate is exactly Mathlib's cardinality statement. -/
theorem hasOrder_iff_card {S : Array (Perm n)} {N : Nat} :
    HasOrder S N ↔ Nat.card (closure S) = N := by
  classical
  constructor
  · rintro ⟨f⟩
    let e : {p : Perm n // Generated S p} ≃ Fin N :=
      ⟨f.toFun, f.invFun, f.left_inv, f.right_inv⟩
    rw [← Nat.card_congr (generatedEquiv S), Nat.card_congr e, Nat.card_fin]
  · intro h
    let e := (generatedEquiv S).trans
      (Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using h))
    exact ⟨⟨e, e.symm, e.symm_apply_apply, e.apply_symm_apply⟩⟩

end Hex.PermGroup
