/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Coset.Transversal

public section

namespace Hex.PermGroup

namespace Group

/-- The exact index for a contained subgroup. Integrality follows from the
transversal product decomposition, not from truncated division alone. -/
@[expose] def index (G H : Group n) (_h : H.IsSubgroup G) : Nat := G.order / H.order

end Group

namespace LeftTransversal

variable {G H : Group n}

theorem count (t : LeftTransversal G H) (h : H.IsSubgroup G) : t.reps.size = G.index H h := by
  rw [Group.index, t.order_eq h, Nat.mul_div_cancel _ H.order_pos]

/-- Distinct stored cosets share no permutation, even if `H` is not normal. -/
theorem disjoint (t : LeftTransversal G H) {i j : Fin t.reps.size} (hne : i ≠ j) (p : Perm n) :
    ¬ (Generated H.generators (t.reps[i.val].val.inv.comp p) ∧
      Generated H.generators (t.reps[j.val].val.inv.comp p)) := by
  rintro ⟨hi, hj⟩
  have hei := (LeftCoset.eq_iff H p t.reps[i.val].val).mpr hi
  have hej := (LeftCoset.eq_iff H p t.reps[j.val].val).mpr hj
  exact hne (t.class_injective (hei.symm.trans hej))

end LeftTransversal

namespace Group

theorem exists_transversal (G H : Group n) : Nonempty (LeftTransversal G H) := by
  obtain ⟨c, hc⟩ := (Action.leftCosets G H).exists_orbit (LeftCoset.mk H (Perm.id n))
  exact ⟨LeftTransversal.ofOrbit c hc⟩

theorem index_mul_order (G H : Group n) (h : H.IsSubgroup G) : G.index H h * H.order = G.order := by
  obtain ⟨t⟩ := G.exists_transversal H
  rw [← t.count h]
  exact (t.order_eq h).symm

theorem index_pos (G H : Group n) (h : H.IsSubgroup G) : 0 < G.index H h := by
  have he := G.index_mul_order H h
  have hp := G.order_pos
  by_cases hi : G.index H h = 0
  · simp [hi] at he
    omega
  · omega

theorem coset_count (G H : Group n) (h : H.IsSubgroup G) (c : Action.Orbit G (LeftCoset H))
    (hc : c.Valid (Action.leftCosets G H) (LeftCoset.mk H (Perm.id n))) :
    c.objects.size = G.index H h := by
  simpa [LeftTransversal.ofOrbit] using (LeftTransversal.ofOrbit c hc).count h

theorem cosetLimit_false (G H : Group n) (h : H.IsSubgroup G)
    (e : Action.OrbitLimit (Action.leftCosets G H) (LeftCoset.mk H (Perm.id n)) (G.index H h)) : False := by
  obtain ⟨c, hc⟩ := (Action.leftCosets G H).exists_orbit (LeftCoset.mk H (Perm.id n))
  have he := e.tooSmall c hc
  rw [G.coset_count H h c hc] at he
  exact Nat.lt_irrefl _ he

/-- Traverse the coset orbit with precisely the known index as capacity.
The public wrapper checks the caller's cap before invoking this helper. -/
@[expose] def leftTransversal (G H : Group n) (h : H.IsSubgroup G) : LeftTransversal G H :=
  match (Action.leftCosets G H).breadthFirst (LeftCoset.mk H (Perm.id n)) (G.index H h) with
  | .ok c => LeftTransversal.ofOrbit c.val c.property.1
  | .error e => False.elim (G.cosetLimit_false H h e)

/-- Complete deterministic left transversal, or an exact size-limit result
before allocation. The representatives need not be canonical across inputs. -/
@[expose] def leftCosetsWith (cap : Nat) (G H : Group n) (h : H.IsSubgroup G) :
    Except SizeLimit (LeftTransversal G H) :=
  if G.index H h ≤ cap then .ok (G.leftTransversal H h)
  else .error ⟨G.index H h, cap⟩

theorem leftCosetsWith_ok (cap : Nat) (G H : Group n) (h : H.IsSubgroup G) :
    (∃ t, leftCosetsWith cap G H h = .ok t) ↔ G.index H h ≤ cap := by
  unfold leftCosetsWith
  split <;> simp_all

theorem leftCosetsWith_error (cap : Nat) (G H : Group n) (h : H.IsSubgroup G) :
    leftCosetsWith cap G H h = .error ⟨G.index H h, cap⟩ ↔ cap < G.index H h := by
  unfold leftCosetsWith
  split <;> simp_all

theorem leftCosetsWith_spec (cap : Nat) (G H : Group n) (h : H.IsSubgroup G)
    (t : LeftTransversal G H) (ht : leftCosetsWith cap G H h = .ok t) :
    t.reps.size = G.index H h ∧ t.reps.size ≤ cap ∧ G.order = t.reps.size * H.order := by
  have hc := (leftCosetsWith_ok cap G H h).mp ⟨t, ht⟩
  exact ⟨t.count h, by rwa [t.count h], t.order_eq h⟩

end Group

end Hex.PermGroup
