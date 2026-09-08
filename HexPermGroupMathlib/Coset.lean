/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Coset.Right
public import HexPermGroupMathlib.Subgroup
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.Index

public section

open scoped Pointwise

namespace Hex.PermGroup

/-- Computational coset equality agrees with Mathlib left cosets. -/
theorem LeftCoset.eq_spec (H : Group n) (p q : Perm n) : LeftCoset.mk H p = LeftCoset.mk H q ↔
    p.toEquiv • (closure H.generators : Set (Equiv.Perm (Fin n))) =
      q.toEquiv • (closure H.generators : Set (Equiv.Perm (Fin n))) := by
  rw [LeftCoset.eq_iff]
  calc
    Generated H.generators (q.inv.comp p) ↔ q.toEquiv⁻¹ * p.toEquiv ∈ closure H.generators := by
      simpa using (generated_iff_mem (S := H.generators) (p := q.inv.comp p))
    _ ↔ q.toEquiv • (closure H.generators : Set (Equiv.Perm (Fin n))) =
        p.toEquiv • (closure H.generators : Set (Equiv.Perm (Fin n))) :=
      (leftCoset_eq_iff (closure H.generators) (x := q.toEquiv) (y := p.toEquiv)).symm
    _ ↔ _ := eq_comm

/-- The exact division used by the executable API is Mathlib's relative index. -/
theorem Group.index_spec (G H : Group n) (h : H.IsSubgroup G) :
    G.index H h = (closure H.generators).relIndex (closure G.generators) := by
  have hle : closure H.generators ≤ closure G.generators :=
    (Group.isSubgroup_spec H G).mp ((Group.isSubgroup_iff H G).mpr h)
  let K := (closure H.generators).subgroupOf (closure G.generators)
  have hc : Nat.card K = H.order :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans H.order_card.symm
  change G.order / H.order = K.index
  rw [G.order_card, ← K.index_mul_card, hc, Nat.mul_div_cancel _ H.order_pos]

namespace LeftTransversal

variable {G H : Group n} (t : LeftTransversal G H)

/-- The returned cosets cover exactly the larger Mathlib subgroup. -/
theorem cosets_spec (h : H.IsSubgroup G) (p : Perm n) :
    (∃ i : Fin t.reps.size, p.toEquiv ∈
      t.reps[i.val].val.toEquiv • (closure H.generators : Set (Equiv.Perm (Fin n)))) ↔
        p.toEquiv ∈ closure G.generators := by
  simp only [mem_leftCoset_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨i, hp⟩
    have hsmall : Generated H.generators (t.reps[i.val].val.inv.comp p) :=
      generated_iff_mem.mpr (by simpa using hp)
    have hlarge := t.reps[i.val].property.comp (h _ hsmall)
    have he : t.reps[i.val].val.comp (t.reps[i.val].val.inv.comp p) = p := by
      simp [← Perm.comp_assoc]
    exact generated_iff_mem.mp (he ▸ hlarge)
  · intro hp
    obtain ⟨i, hi⟩ := t.covers ⟨p, generated_iff_mem.mpr hp⟩
    refine ⟨i, ?_⟩
    have hh := (LeftCoset.eq_iff H p t.reps[i.val].val).mp hi.symm
    simpa using generated_iff_mem.mp hh

theorem disjoint_spec {i j : Fin t.reps.size} (hne : i ≠ j) :
    Disjoint (t.reps[i.val].val.toEquiv • (closure H.generators : Set (Equiv.Perm (Fin n))))
      (t.reps[j.val].val.toEquiv • (closure H.generators : Set (Equiv.Perm (Fin n)))) := by
  apply Set.disjoint_left.mpr
  intro p hi hj
  rw [mem_leftCoset_iff] at hi hj
  apply t.disjoint hne (Perm.ofEquiv p)
  constructor
  · exact generated_iff_mem.mpr (by simpa using hi)
  · exact generated_iff_mem.mpr (by simpa using hj)

end LeftTransversal

end Hex.PermGroup
