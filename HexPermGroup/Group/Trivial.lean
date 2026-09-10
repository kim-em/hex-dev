/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Rank

public section

namespace Hex.PermGroup.Group

/-- Exact order one is equivalent to having only the identity element. -/
theorem order_one (G : Group n) : G.order = 1 ↔ ∀ p, Generated G.generators p → p = Perm.id n := by
  constructor
  · intro h p hp
    let e : Element G := ⟨p, hp⟩
    have he : G.rank e = G.rank (Element.id G) := by
      apply Fin.ext
      have ha := (G.rank e).isLt
      have hb := (G.rank (Element.id G)).isLt
      omega
    have hh := congrArg G.unrank he
    rw [G.unrank_rank, G.unrank_rank] at hh
    exact congrArg Subtype.val hh
  · intro h
    have he (k : Fin G.order) : k = G.rank (Element.id G) := by
      rw [← G.rank_unrank k]
      exact congrArg G.rank (Subtype.ext (h _ (G.unrank k).property))
    have hp := G.order_pos
    by_cases hn : G.order = 1
    · exact hn
    have ht : 1 < G.order := by omega
    have hz := he ⟨0, hp⟩
    have ho := he ⟨1, ht⟩
    have hh := congrArg Fin.val (hz.trans ho.symm)
    simp at hh

@[expose] def isTrivial (G : Group n) : Bool := decide (G.order = 1)

theorem isTrivial_iff (G : Group n) : G.isTrivial = true ↔ ∀ p, Generated G.generators p → p = Perm.id n := by
  rw [isTrivial, decide_eq_true_eq, G.order_one]

end Hex.PermGroup.Group
