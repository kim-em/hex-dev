/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Group
public import HexPermGroup.Build
public import HexPermGroupMathlib.Check

public section

namespace Hex.PermGroup

instance (G : Group n) : _root_.Group (Element G) where
  mul := Element.comp
  one := Element.id G
  inv := Element.inv
  mul_assoc := Element.comp_assoc
  one_mul := Element.id_comp
  mul_one := Element.comp_id
  inv_mul_cancel := Element.inv_comp_self

/-- Membership and exact order of a checked computational group agree with its
Mathlib subgroup, using the original generator presentation. -/
theorem Group.contains_spec (G : Group n) (p : Perm n) :
    G.contains p = true ↔ p.toEquiv ∈ closure G.generators :=
  (G.contains_iff p).trans generated_iff_mem

theorem Group.order_card (G : Group n) : G.order = Nat.card (closure G.generators) :=
  checkChain_card G.valid

/-- The deterministic constructor has exact Mathlib membership and cardinality
for every input, with no assumed group order or successful search hypothesis. -/
theorem Group.ofGenerators_spec (S : Array (Perm n)) :
    (∀ p : Perm n, (ofGenerators S).contains p = true ↔ p.toEquiv ∈ closure S) ∧
      (ofGenerators S).order = Nat.card (closure S) :=
  ⟨(ofGenerators S).contains_spec, (ofGenerators S).order_card⟩

/-- Elements correspond by their permutation values, preserving multiplication. -/
@[expose] def Element.equiv (G : Group n) : Element G ≃* closure G.generators where
  toFun p := ⟨p.val.toEquiv, generated_iff_mem.mp p.property⟩
  invFun e := ⟨Perm.ofEquiv e.val, generated_iff_mem.mpr (by
    simpa only [Perm.toEquiv_ofEquiv] using e.property)⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv e := by
    apply Subtype.ext
    simp
  map_mul' p q := by
    apply Subtype.ext
    exact Perm.toEquiv_comp p.val q.val

end Hex.PermGroup
