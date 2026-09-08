/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.Closure
public import HexPermGroup.Normal.Core
public import HexPermGroupMathlib.Subgroup

public section

namespace Hex.PermGroup.Group

/-- The insertion trace lies in every mathematical normal subgroup containing
the input, without requiring an executable presentation of that subgroup. -/
theorem normalClosure_le_subgroup (G H : Group n) (h : H.IsSubgroup G)
    (N : Subgroup (closure G.generators)) [N.Normal]
    (hN : (closure H.generators).subgroupOf (closure G.generators) ≤ N) :
    (closure (G.normalClosure H h).generators).subgroupOf (closure G.generators) ≤ N := by
  let P : Perm n → Prop := fun p => ∃ hp : Generated G.generators p,
    (⟨p.toEquiv, generated_iff_mem.mp hp⟩ : closure G.generators) ∈ N
  have hi : P (Perm.id n) := by
    refine ⟨.id, ?_⟩
    convert N.one_mem using 1
    congr 1
    simp
  have hm : ∀ p q, P p → P q → P (p.comp q) := by
    rintro p q ⟨hp, hpm⟩ ⟨hq, hqm⟩
    exact ⟨hp.comp hq, by simpa using N.mul_mem hpm hqm⟩
  have hv : ∀ p, P p → P p.inv := by
    rintro p ⟨hp, hpm⟩
    refine ⟨hp.inv, ?_⟩
    convert N.inv_mem hpm using 1
    congr 1
    simp
  have hc : ∀ g p, Generated G.generators g → P p → P (g.conj p) := by
    rintro g p hg ⟨hp, hpm⟩
    refine ⟨hg.comp (hp.comp hg.inv), ?_⟩
    have hh := (inferInstance : N.Normal).conj_mem _ hpm
      (⟨g.toEquiv, generated_iff_mem.mp hg⟩ : closure G.generators)
    convert hh using 1
    congr 1
    simp [Perm.conj, mul_assoc]
  have hH : ∀ p, Generated H.generators p → P p := by
    intro p hp
    exact ⟨h p hp, hN (generated_iff_mem.mp hp)⟩
  intro e he
  have hp : Generated (G.normalClosure H h).generators (Perm.ofEquiv e.val) :=
    generated_iff_mem.mpr (by simpa [Subgroup.mem_subgroupOf] using he)
  obtain ⟨_, hm⟩ := Normal.replay_lift (G.normalClosureCert H h).replayed hi hm hv hc hH _ hp
  simpa using hm

/-- The computational normal closure is Mathlib's normal closure inside the
ambient generated subgroup. All conjugation takes place in that group. -/
theorem normalClosure_spec (G H : Group n) (h : H.IsSubgroup G) :
    (closure (G.normalClosure H h).generators).subgroupOf (closure G.generators) =
      Subgroup.normalClosure
        ((closure H.generators).subgroupOf (closure G.generators) : Set (closure G.generators)) := by
  apply le_antisymm
  · exact G.normalClosure_le_subgroup H h _ Subgroup.subset_normalClosure
  · have := (isNormal_spec _ G (G.normalClosure_inside H h)).mp (G.normalClosure_normal H h)
    apply Subgroup.normalClosure_le_normal
    intro e he
    have hp : Generated H.generators (Perm.ofEquiv e.val) :=
      generated_iff_mem.mpr (by simpa [Subgroup.mem_subgroupOf] using he)
    have hh := generated_iff_mem.mp (G.normalClosure_contains H h _ hp)
    simpa [Subgroup.mem_subgroupOf] using hh

/-- Complete intersection replay identifies the core with Mathlib's greatest
normal subgroup contained in the input. -/
theorem core_spec (G H : Group n) (h : H.IsSubgroup G) :
    (closure (G.core H h).generators).subgroupOf (closure G.generators) =
      ((closure H.generators).subgroupOf (closure G.generators)).normalCore := by
  ext e
  change e.val ∈ closure (G.core H h).generators ↔
    ∀ g : closure G.generators, g.val * e.val * g.val⁻¹ ∈ closure H.generators
  constructor
  · intro he g
    have hp : Generated (G.core H h).generators (Perm.ofEquiv e.val) :=
      generated_iff_mem.mpr (by simpa using he)
    have hg : Generated G.generators (Perm.ofEquiv g.val) :=
      generated_iff_mem.mpr (by simp)
    have hh := generated_iff_mem.mp ((G.mem_core H h _).mp hp _ hg)
    simpa [Perm.conj, mul_assoc] using hh
  · intro he
    have hp : Generated (G.core H h).generators (Perm.ofEquiv e.val) := by
      apply (G.mem_core H h _).mpr
      intro g hg
      apply generated_iff_mem.mpr
      simpa [Perm.conj, mul_assoc] using he ⟨g.toEquiv, generated_iff_mem.mp hg⟩
    simpa using generated_iff_mem.mp hp

end Hex.PermGroup.Group
