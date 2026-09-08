/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Subgroup

public section

namespace Hex.PermGroup

/-- An executable left action with laws for every group element. Its argument
is a permutation value with membership evidence, independent of word programs. -/
structure Action (G : Group n) (α : Type u) where
  act : Element G → α → α
  id_act : ∀ x, act (Element.id G) x = x
  comp_act : ∀ p q x, act (p.comp q) x = act p (act q x)

namespace Action

variable {G : Group n} {α : Type u} (a : Action G α)

@[simp] theorem act_id (x : α) : a.act (Element.id G) x = x := a.id_act x

theorem act_comp (p q : Element G) (x : α) :
    a.act (p.comp q) x = a.act p (a.act q x) := a.comp_act p q x

@[simp] theorem act_inv (p : Element G) (x : α) : a.act p (a.act p.inv x) = x := by
  rw [← act_comp, Element.comp_inv_self, act_id]

@[simp] theorem inv_act (p : Element G) (x : α) : a.act p.inv (a.act p x) = x := by
  rw [← act_comp, Element.inv_comp_self, act_id]

theorem act_injective (p : Element G) {x y : α} (h : a.act p x = a.act p y) : x = y := by
  have := congrArg (a.act p.inv) h
  simpa using this

theorem act_surjective (p : Element G) (x : α) : ∃ y, a.act p y = x :=
  ⟨a.act p.inv x, a.act_inv p x⟩

/-- Restrict an action to a checked subgroup, without changing its values. -/
@[expose] def restrict (H : Group n) (h : H.IsSubgroup G) : Action H α where
  act p x := a.act ⟨p.val, h p.val p.property⟩ x
  id_act := a.id_act
  comp_act p q x := a.comp_act ⟨p.val, h p.val p.property⟩ ⟨q.val, h q.val q.property⟩ x

/-- Componentwise action on fixed-length tuples; repeated entries are retained. -/
@[expose] def vectors (k : Nat) : Action G (Vector α k) where
  act p xs := xs.map (a.act p)
  id_act xs := by apply Vector.ext; intro i hi; simp
  comp_act p q xs := by apply Vector.ext; intro i hi; simp [act_comp]

/-- The natural action on the declared point domain, including degree zero. -/
@[expose] def natural (G : Group n) : Action G (Fin n) where
  act p x := p.val.get x
  id_act := Perm.get_id
  comp_act p q x := Perm.get_comp p.val q.val x

@[expose] def tuples (G : Group n) (k : Nat) : Action G (Vector (Fin n) k) :=
  (natural G).vectors k

/-- Bit vectors represent subsets. Moving points forward reads their membership
at inverse images, so this obeys the same left-action composition convention. -/
@[expose] def subsets (G : Group n) : Action G (Vector Bool n) where
  act p xs := Hex.Vector.ofFn' fun x => xs[p.val.inv.get x]
  id_act xs := by apply Vector.ext; intro i hi; simp
  comp_act p q xs := by
    apply Vector.ext
    intro i hi
    simp [Perm.inv_comp]

/-- A subset element moves to the forward image of its original point. -/
@[simp] theorem subsets_apply (G : Group n) (p : Element G) (xs : Vector Bool n) (x : Fin n) :
    ((subsets G).act p xs).get (p.val.get x) = xs.get x := by
  change (Hex.Vector.ofFn' fun y => xs[p.val.inv.get y])[(p.val.get x).val] = xs[x.val]
  simp

/-- A predicate invariant under the signed input generators is invariant under
every group element. This also applies when the action has a nontrivial kernel. -/
theorem invariant (P : α → Prop)
    (h : ∀ i : Fin G.generators.size, ∀ x,
      P x ↔ P (a.act ⟨G.generators[i.val], .generator (Array.getElem_mem i.isLt)⟩ x))
    (p : Element G) (x : α) : P x ↔ P (a.act p x) := by
  obtain ⟨p, hp⟩ := p
  induction hp generalizing x with
  | id =>
    change P x ↔ P (a.act (Element.id G) x)
    rw [act_id]
  | generator hp =>
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hp
    exact h ⟨i, hi⟩ x
  | @comp p q hp hq ihp ihq =>
    exact (ihq x).trans ((ihp (a.act ⟨q, hq⟩ x)).trans (by
      rw [show (⟨p.comp q, .comp hp hq⟩ : Element G) =
        Element.comp ⟨p, hp⟩ ⟨q, hq⟩ from rfl, act_comp]))
  | @inv p hp ih =>
    have he := (ih (a.act (Element.inv ⟨p, hp⟩) x)).symm
    rw [act_inv] at he
    exact he

end Action

end Hex.PermGroup
