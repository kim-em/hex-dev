/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.Solvable
public import HexPermGroupMathlib.Derived
public import Mathlib.GroupTheory.Solvable

public section

namespace Hex.PermGroup.Group

theorem order_one_spec (G : Group n) : G.order = 1 ↔ closure G.generators = ⊥ := by
  constructor
  · intro h
    apply le_antisymm ?_ bot_le
    intro e he
    have hp : Generated G.generators (Perm.ofEquiv e) := generated_iff_mem.mpr (by simpa using he)
    have hh := congrArg Perm.toEquiv ((G.order_one.mp h) _ hp)
    simpa using hh
  · intro h
    apply G.order_one.mpr
    intro p hp
    apply Perm.equiv.injective
    have hh := generated_iff_mem.mp hp
    simpa [h, Perm.equiv] using hh

/-- Every computational series term is the image of the corresponding
Mathlib derived-series subgroup under the ambient inclusion. -/
theorem derivedAt_spec (G : Group n) (k : Nat) :
    closure (G.derivedAt k).generators =
      (_root_.derivedSeries (closure G.generators) k).map (closure G.generators).subtype := by
  induction k with
  | zero =>
    change closure G.generators = Subgroup.map (closure G.generators).subtype ⊤
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  | succ k ih =>
    change closure (G.derivedAt k).derived.generators = _
    rw [derived_spec, ih, _root_.derivedSeries_succ, Subgroup.map_commutator]

/-- Solvability of the executable group is exactly Mathlib solvability of its
generated subgroup; negative certificates therefore prove nonsolvability. -/
theorem solvable_spec (G : Group n) : G.IsSolvable ↔ _root_.Group.IsSolvable (closure G.generators) := by
  rw [_root_.Group.isSolvable_def]
  unfold IsSolvable
  apply exists_congr
  intro k
  rw [(G.derivedAt k).order_one_spec, G.derivedAt_spec]
  exact Subgroup.map_eq_bot_iff_of_injective _ Subtype.val_injective

theorem isSolvable_spec (G : Group n) : G.isSolvable = true ↔ _root_.Group.IsSolvable (closure G.generators) :=
  G.isSolvable_iff.trans G.solvable_spec

end Hex.PermGroup.Group
