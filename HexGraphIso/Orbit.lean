/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Generated

public section

namespace Hex.GraphIso.Aut

variable {n k : Nat}

/-- The orbit relation for the full pointwise stabilizer of a base. -/
def Orbit (G : Colored n k) (base : List (Fin n)) (u v : Fin n) : Prop :=
  ∃ p, IsIso G G p ∧ Perm.Fixes base p ∧ p.get u = v

namespace Orbit

variable {G : Colored n k} {base : List (Fin n)} {u v w : Fin n}

theorem refl (G : Colored n k) (base : List (Fin n)) (u : Fin n) : Orbit G base u u :=
  ⟨Perm.id n, IsIso.refl G, Perm.Fixes.id base, by simp⟩

theorem trans (h : Orbit G base u v) (h' : Orbit G base v w) : Orbit G base u w := by
  obtain ⟨p, hp, hpf, hpu⟩ := h
  obtain ⟨q, hq, hqf, hqv⟩ := h'
  exact ⟨q.comp p, hp.trans hq, hqf.comp hpf, by simp [hpu, hqv]⟩

theorem symm (h : Orbit G base u v) : Orbit G base v u := by
  obtain ⟨p, hp, hpf, rfl⟩ := h
  exact ⟨p.inv, hp.symm, hpf.inv, by simp⟩

end Orbit

end Hex.GraphIso.Aut
