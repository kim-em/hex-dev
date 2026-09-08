/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Predicates
public import HexPermGroupMathlib.Group
public import HexPermGroupMathlib.Orbit
public import Mathlib.Algebra.Group.Subgroup.Basic

public section

namespace Hex.PermGroup.Group

theorem isSubgroup_spec (H G : Group n) :
    H.isSubgroup G = true ↔ closure H.generators ≤ closure G.generators := by
  rw [isSubgroup_iff]
  constructor
  · intro h e he
    have hp : Generated H.generators (Perm.ofEquiv e) := generated_iff_mem.mpr (by simpa using he)
    simpa using generated_iff_mem.mp (h _ hp)
  · intro h p hp
    exact generated_iff_mem.mpr (h (generated_iff_mem.mp hp))

theorem sameGroup_spec (G H : Group n) :
    G.sameGroup H = true ↔ closure G.generators = closure H.generators := by
  rw [sameGroup, Bool.and_eq_true, isSubgroup_spec, isSubgroup_spec]
  exact le_antisymm_iff.symm

theorem join_spec (G H : Group n) :
    closure (G.join H).generators = closure G.generators ⊔ closure H.generators := by
  apply le_antisymm
  · change Subgroup.closure (G := Equiv.Perm (Fin n)) _ ≤ _
    apply (Subgroup.closure_le _).mpr
    rintro e ⟨p, hp, rfl⟩
    simp only [join, generators_ofGenerators, Array.mem_append] at hp
    rcases hp with hp | hp
    · exact (show closure G.generators ≤ closure G.generators ⊔ closure H.generators from le_sup_left)
        (generated_iff_mem.mp (.generator hp))
    · exact (show closure H.generators ≤ closure G.generators ⊔ closure H.generators from le_sup_right)
        (generated_iff_mem.mp (.generator hp))
  · apply sup_le
    · exact (isSubgroup_spec G (G.join H)).mp
        ((isSubgroup_iff G (G.join H)).mpr (left_subgroup_join G H))
    · exact (isSubgroup_spec H (G.join H)).mp
        ((isSubgroup_iff H (G.join H)).mpr (right_subgroup_join G H))

theorem orbit_spec (G : Group n) (a b : Fin n) :
    b ∈ G.orbit a ↔ ∃ e : Equiv.Perm (Fin n), e ∈ closure G.generators ∧ e a = b := by
  rw [mem_orbit]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p.toEquiv, generated_iff_mem.mp hp, he⟩
  · rintro ⟨e, he, hx⟩
    exact ⟨Perm.ofEquiv e, generated_iff_mem.mpr (by simpa using he), by simpa using hx⟩

theorem orbits_spec (G : Group n) (a b : Fin n) :
    (∃ points ∈ G.orbits, a ∈ points ∧ b ∈ points) ↔
      ∃ e : Equiv.Perm (Fin n), e ∈ closure G.generators ∧ e a = b := by
  rw [← orbit_spec]
  constructor
  · rintro ⟨points, hp, ha, hb⟩
    obtain ⟨x, rfl⟩ := (G.mem_orbits points).mp hp
    simpa only [G.orbit_eq x a ha] using hb
  · intro hb
    exact ⟨G.orbit a, G.orbit_mem_orbits a, G.self_mem_orbit a, hb⟩

theorem stabilizer_spec (G : Group n) (a : Fin n) :
    closure (G.stabilizer a).generators =
      closure G.generators ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) a := by
  ext e
  simpa [generated_iff_mem, MulAction.mem_stabilizer_iff] using mem_stabilizer G a (Perm.ofEquiv e)

theorem pointwise_spec (G : Group n) (points : List (Fin n)) (e : Equiv.Perm (Fin n)) :
    e ∈ closure (G.pointwise points).generators ↔ e ∈ closure G.generators ∧ ∀ a ∈ points, e a = a := by
  simpa [generated_iff_mem] using mem_pointwise G points (Perm.ofEquiv e)

theorem conjugate_spec (p : Perm n) (G : Group n) (e : Equiv.Perm (Fin n)) :
    e ∈ closure (conjugate p G).generators ↔
      p.toEquiv⁻¹ * e * p.toEquiv ∈ closure G.generators := by
  simpa [generated_iff_mem, Perm.conj, mul_assoc] using mem_conjugate p G (Perm.ofEquiv e)

theorem isAbelian_spec (G : Group n) : G.isAbelian = true ↔
    ∀ p q : closure G.generators, p * q = q * p := by
  rw [isAbelian_iff]
  constructor
  · intro h p q
    apply Subtype.ext
    have hp : Generated G.generators (Perm.ofEquiv p.val) := generated_iff_mem.mpr (by simp)
    have hq : Generated G.generators (Perm.ofEquiv q.val) := generated_iff_mem.mpr (by simp)
    simpa using congrArg Perm.toEquiv (h _ _ hp hq)
  · intro h p q hp hq
    apply Perm.equiv.injective
    change (p.comp q).toEquiv = (q.comp p).toEquiv
    rw [Perm.toEquiv_comp, Perm.toEquiv_comp]
    exact congrArg (fun p : closure G.generators => p.val)
      (h ⟨p.toEquiv, generated_iff_mem.mp hp⟩ ⟨q.toEquiv, generated_iff_mem.mp hq⟩)

theorem isNormal_spec (H G : Group n) (h : H.IsSubgroup G) :
    H.isNormal G h = true ↔ ((closure H.generators).subgroupOf (closure G.generators)).Normal := by
  rw [isNormal_iff]
  constructor
  · intro hc
    constructor
    intro q hq p
    have hp : Generated G.generators (Perm.ofEquiv p.val) := generated_iff_mem.mpr (by simp)
    have hq' : Generated H.generators (Perm.ofEquiv q.val) :=
      generated_iff_mem.mpr (by simpa [Subgroup.mem_subgroupOf] using hq)
    have he := generated_iff_mem.mp (hc _ _ hp hq')
    simpa [Perm.conj, mul_assoc, Subgroup.mem_subgroupOf] using he
  · intro hc p q hp hq
    let pp : closure G.generators := ⟨p.toEquiv, generated_iff_mem.mp hp⟩
    let qq : closure G.generators := ⟨q.toEquiv, generated_iff_mem.mp (h q hq)⟩
    have hqq : qq ∈ (closure H.generators).subgroupOf (closure G.generators) :=
      generated_iff_mem.mp hq
    have he := hc.conj_mem qq hqq pp
    apply generated_iff_mem.mpr
    simpa [pp, qq, Perm.conj, mul_assoc, Subgroup.mem_subgroupOf] using he

theorem isTransitive_spec (G : Group n) : G.isTransitive = true ↔
    0 < n ∧ ∀ a b : Fin n, ∃ e : closure G.generators, e.val a = b := by
  rw [isTransitive_iff]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    intro a b
    obtain ⟨p, hp, he⟩ := h a b
    exact ⟨⟨p.toEquiv, generated_iff_mem.mp hp⟩, he⟩
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    intro a b
    obtain ⟨e, he⟩ := h a b
    exact ⟨Perm.ofEquiv e.val, generated_iff_mem.mpr (by simp), by simpa using he⟩

end Hex.PermGroup.Group
