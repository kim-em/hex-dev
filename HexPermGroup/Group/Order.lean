/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Coset.Build

public section

namespace Hex.PermGroup

namespace Group

variable {G H : Group n}

/-- Subgroup containment bounds exact order, without enumerating either group
in the executable operation. -/
theorem IsSubgroup.order_le (h : H.IsSubgroup G) : H.order ≤ G.order := by
  have hi := G.index_pos H h
  have he := G.index_mul_order H h
  calc
    H.order = 1 * H.order := by simp
    _ ≤ G.index H h * H.order := Nat.mul_le_mul_right H.order hi
    _ = G.order := he

/-- Index one means equality of the represented groups, independently of
generator presentation. The transversal exists only in this erased proof. -/
theorem index_one (h : H.IsSubgroup G) : G.index H h = 1 ↔ SameGroup H G := by
  constructor
  · intro hi
    obtain ⟨t⟩ := G.exists_transversal H
    have ht : t.reps.size = 1 := (t.count h).trans hi
    intro p
    refine ⟨h p, ?_⟩
    intro hp
    obtain ⟨i, hi⟩ := t.covers ⟨p, hp⟩
    obtain ⟨j, hj⟩ := t.covers (Element.id G)
    have hij : i = j := Fin.ext (by have hi := i.isLt; have hj := j.isLt; omega)
    apply (LeftCoset.eq_id H p).mp
    exact hi.symm.trans (hij ▸ hj)
  · intro hs
    have hg : G.IsSubgroup H := fun p hp => (hs p).mpr hp
    have he : G.order = H.order := Nat.le_antisymm hg.order_le h.order_le
    apply Nat.mul_right_cancel H.order_pos
    simpa only [Nat.one_mul, he] using G.index_mul_order H h

/-- A strict subgroup has index at least two, so every strict increase or
decrease changes order by a factor of at least two. -/
theorem IsSubgroup.order_double (h : H.IsSubgroup G) (hne : ¬SameGroup H G) :
    2 * H.order ≤ G.order := by
  have hi := G.index_pos H h
  have hn : G.index H h ≠ 1 := fun he => hne ((index_one h).mp he)
  have htwo : 2 ≤ G.index H h := by omega
  calc
    2 * H.order ≤ G.index H h * H.order := Nat.mul_le_mul_right H.order htwo
    _ = G.order := G.index_mul_order H h

theorem IsSubgroup.order_lt (h : H.IsSubgroup G) (hne : ¬SameGroup H G) : H.order < G.order := by
  have hd := h.order_double hne
  have hp := H.order_pos
  omega

/-- Under containment, equality of exact orders certifies subgroup equality. -/
theorem IsSubgroup.order_eq_iff (h : H.IsSubgroup G) : H.order = G.order ↔ SameGroup H G := by
  constructor
  · intro he
    by_cases hs : SameGroup H G
    · exact hs
    · have hl := h.order_lt hs
      omega
  · intro hs
    have hg : G.IsSubgroup H := fun p hp => (hs p).mpr hp
    exact Nat.le_antisymm h.order_le hg.order_le

end Group

theorem SameGroup.order_eq {G H : Group n} (h : SameGroup G H) : G.order = H.order :=
  (Group.IsSubgroup.order_eq_iff (show G.IsSubgroup H from fun p hp => (h p).mp hp)).mpr h

end Hex.PermGroup
