/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Equitable.Basic

public section

/-!
Adjacency preservation by disjoint transpositions. A pair relation specifies
the two members of each transposition. Fixed vertices must have equal
adjacency to those members, and adjacency between pairs must agree under
simultaneous exchange.
-/

namespace Hex.GraphIso.Nauty

/-- A map given by transpositions preserves adjacency exactly when fixed
vertices see each pair alike and the adjacency between pairs agrees under
simultaneous exchange. The cross conditions include a pair compared with
itself, expressing equal loops and symmetry on that pair. -/
theorem flip_iff {α : Type} {R : α → α → Bool} {f : α → α}
    {P : α → α → Prop}
    (hsymm : ∀ u v, R u v = R v u)
    (hswap : ∀ u v, P u v → f u = v ∧ f v = u)
    (hcover : ∀ z, f z = z ∨ ∃ u v, P u v ∧ (z = u ∨ z = v)) :
    (∀ z w, R (f z) (f w) = R z w) ↔
      (∀ z, f z = z → ∀ u v, P u v → R z u = R z v) ∧
      (∀ u v x y, P u v → P x y →
        R u x = R v y ∧ R u y = R v x) := by
  constructor
  · intro h
    constructor
    · intro z hz u v hp
      have h' := h z u
      rw [hz, (hswap u v hp).1] at h'
      exact h'.symm
    · intro u v x y hp hq
      obtain ⟨hu, hv⟩ := hswap u v hp
      obtain ⟨hx, hy⟩ := hswap x y hq
      exact ⟨by simpa only [hu, hx] using (h u x).symm,
        by simpa only [hu, hy] using (h u y).symm⟩
  · rintro ⟨hfix, hcross⟩ z w
    rcases hcover z with hz | ⟨u, v, hp, hz⟩
    · rcases hcover w with hw | ⟨x, y, hq, hw⟩
      · rw [hz, hw]
      · have hs := hswap x y hq
        have hf := hfix z hz x y hq
        rcases hw with hw | hw <;> rw [hw] <;> grind
    · have hs := hswap u v hp
      rcases hcover w with hw | ⟨x, y, hq, hw⟩
      · have hf := hfix w hw u v hp
        have hu := hsymm w u
        have hv := hsymm w v
        rcases hz with hz | hz <;> rw [hz] <;> grind
      · have ht := hswap x y hq
        have hc := hcross u v x y hp hq
        rcases hz with hz | hz <;> rcases hw with hw | hw <;>
          rw [hz, hw] <;> grind

/-- The transposition criterion on the bounded vertex indices of a graph. -/
theorem flip_bits {ctx : Ctx n} {f : Nat → Nat} {P : Nat → Nat → Prop}
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hbound : ∀ z, z < n → f z < n)
    (hswap : ∀ u v, P u v → f u = v ∧ f v = u)
    (hcover : ∀ z, z < n →
      f z = z ∨ ∃ u v, u < n ∧ v < n ∧ P u v ∧ (z = u ∨ z = v))
    (hfix : ∀ z, z < n → f z = z → ∀ u v, P u v →
      (ctx.g[z]!).mem u = (ctx.g[z]!).mem v)
    (hcross : ∀ u v x y, P u v → P x y →
      (ctx.g[u]!).mem x = (ctx.g[v]!).mem y ∧
      (ctx.g[u]!).mem y = (ctx.g[v]!).mem x) :
    ∀ z w, z < n → w < n →
      (ctx.g[f z]!).mem (f w) = (ctx.g[z]!).mem w := by
  let f' : Fin n → Fin n := fun z => ⟨f z, hbound z z.isLt⟩
  have hs : ∀ u v : Fin n, P u v → f' u = v ∧ f' v = u := by
    intro u v hp
    obtain ⟨hu, hv⟩ := hswap u v hp
    exact ⟨Fin.ext hu, Fin.ext hv⟩
  have hc : ∀ z : Fin n,
      f' z = z ∨ ∃ u v : Fin n, P u v ∧ (z = u ∨ z = v) := by
    intro z
    rcases hcover z z.isLt with hz | ⟨u, v, hu, hv, hp, hz⟩
    · exact Or.inl (Fin.ext hz)
    · refine Or.inr ⟨⟨u, hu⟩, ⟨v, hv⟩, hp, ?_⟩
      exact hz.elim (fun h => Or.inl (Fin.ext h))
        (fun h => Or.inr (Fin.ext h))
  have hb := (flip_iff (R := fun z w : Fin n => (ctx.g[z.val]!).mem w)
    (fun u v => hsymm u v u.isLt v.isLt) hs hc).mpr
      ⟨fun z hz u v hp => hfix z z.isLt (congrArg Fin.val hz) u v hp,
        fun u v x y hp hq => hcross u v x y hp hq⟩
  exact fun z w hz hw => hb ⟨z, hz⟩ ⟨w, hw⟩

end Hex.GraphIso.Nauty
