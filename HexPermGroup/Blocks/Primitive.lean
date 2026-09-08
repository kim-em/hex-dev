/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Blocks
public import HexPermGroup.Predicates

public section

namespace Hex.PermGroup

namespace Partition

theorem eq_discrete (p : Partition n) :
    p = discrete n ↔ ∀ x y, p.Same x y → x = y := by
  constructor
  · rintro rfl x y
    exact (discrete_same x y).mp
  · intro h
    apply ext
    intro x y
    rw [discrete_same]
    exact ⟨h x y, fun he => he ▸ rfl⟩

theorem eq_indiscrete (p : Partition n) :
    p = indiscrete n ↔ ∀ x y, p.Same x y := by
  constructor
  · rintro rfl x y
    exact indiscrete_same x y
  · intro h
    apply ext
    intro x y
    exact ⟨fun _ => indiscrete_same x y, fun _ => h x y⟩

/-- Transitivity transports a nonsingleton block to the block through any
chosen point. Thus every nondiscrete invariant partition is detected there. -/
theorem IsInvariant.nonsingleton {p : Partition n} {G : Group n} (hp : p.IsInvariant G)
    (ht : G.isTransitive = true) (hd : p ≠ discrete n) (a : Fin n) :
    ∃ b, b ≠ a ∧ p.Same a b := by
  have he : ∃ x y, p.Same x y ∧ x ≠ y := by
    by_cases he : ∃ x y, p.Same x y ∧ x ≠ y
    · exact he
    · apply False.elim
      apply hd ((p.eq_discrete).mpr ?_)
      intro x y hxy
      by_cases h : x = y
      · exact h
      · exact False.elim (he ⟨x, y, hxy, h⟩)
  obtain ⟨x, y, hxy, hne⟩ := he
  obtain ⟨g, hg, hga⟩ := (G.isTransitive_iff.mp ht).2 x a
  refine ⟨g.get y, ?_, ?_⟩
  · intro h
    exact hne (g.get_inj (hga.trans h.symm))
  · simpa only [hga] using (hp g hg x y).mp hxy

end Partition

namespace Group

/-- Primitive actions have degree at least two, are transitive, and admit
only the discrete and indiscrete invariant partitions. -/
@[expose] def IsPrimitive (G : Group n) : Prop :=
  2 ≤ n ∧ G.isTransitive = true ∧
    ∀ p : Partition n, p.IsInvariant G → p = Partition.discrete n ∨ p = Partition.indiscrete n

/-- The fixed-point seeded criterion is equivalent to the full invariant
partition condition. Transitivity is essential to the reverse direction. -/
theorem primitive_criterion (G : Group n) (hn : 2 ≤ n) (ht : G.isTransitive = true)
    (a : Fin n) : G.IsPrimitive ↔ ∀ b, b ≠ a → G.blocks [(a, b)] = Partition.indiscrete n := by
  constructor
  · intro h b hb
    rcases h.2.2 (G.blocks [(a, b)]) (G.blocks_invariant _) with hd | hi
    · have hs := G.blocks_seeds [(a, b)] (a, b) (by simp)
      rw [hd, Partition.discrete_same] at hs
      exact False.elim (hb hs.symm)
    · exact hi
  · intro h
    refine ⟨hn, ht, ?_⟩
    intro p hp
    by_cases hd : p = Partition.discrete n
    · exact Or.inl hd
    · obtain ⟨b, hb, hab⟩ := hp.nonsingleton ht hd a
      apply Or.inr
      apply p.eq_indiscrete.mpr
      have hm := G.blocks_least [(a, b)] p.Same p.equivalence
        (fun g hg x y => (hp g hg x y).mp) (by
          intro q hq
          have he : q = (a, b) := by simpa using hq
          exact he ▸ hab)
      rw [h b hb] at hm
      exact fun x y => hm x y (Partition.indiscrete_same x y)

end Group

end Hex.PermGroup
