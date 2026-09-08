/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Group.Order

public section

namespace Hex.PermGroup.Group

/-- Append one generator and rebuild the complete checked chain. Callers can
omit redundant insertions using a complete membership test first. -/
@[expose] def adjoin (H : Group n) (p : Perm n) : Group n :=
  ofGenerators (H.generators.push p)

theorem subgroup_adjoin (H : Group n) (p : Perm n) : H.IsSubgroup (H.adjoin p) := by
  intro q hq
  exact hq.mono fun r hr => .generator (Array.mem_push.mpr (Or.inl hr))

theorem mem_adjoin (H : Group n) (p : Perm n) : Generated (H.adjoin p).generators p :=
  .generator (Array.mem_push.mpr (Or.inr rfl))

/-- Adjoining a generator is the least subgroup containing the old group and
that generator. -/
theorem adjoin_le (H K : Group n) (p : Perm n) :
    (H.adjoin p).IsSubgroup K ↔ H.IsSubgroup K ∧ Generated K.generators p := by
  constructor
  · intro h
    exact ⟨fun q hq => h q (H.subgroup_adjoin p q hq), h p (H.mem_adjoin p)⟩
  · rintro ⟨hH, hp⟩ q hq
    apply hq.mono
    intro r hr
    simp only [adjoin, generators_ofGenerators, Array.mem_push] at hr
    rcases hr with hr | rfl
    · exact hH r (.generator hr)
    · exact hp

theorem order_adjoin (H : Group n) (p : Perm n) (hp : ¬Generated H.generators p) :
    2 * H.order ≤ (H.adjoin p).order := by
  apply (H.subgroup_adjoin p).order_double
  intro h
  exact hp ((h p).mpr (H.mem_adjoin p))

end Hex.PermGroup.Group
