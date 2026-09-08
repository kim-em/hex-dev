/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.Core
public import HexPermGroup.Action.Kernel

public section

namespace Hex.PermGroup

namespace LeftTransversal

variable {G H : Group n}

@[expose] def cosets (t : LeftTransversal G H) : Array (LeftCoset H) :=
  t.reps.map fun p => LeftCoset.mk H p.val

@[simp] theorem cosets_size (t : LeftTransversal G H) : t.cosets.size = t.reps.size := by
  simp [cosets]

theorem mem_cosets (t : LeftTransversal G H) (p : Element G) : LeftCoset.mk H p.val ∈ t.cosets := by
  obtain ⟨i, hi⟩ := t.covers p
  exact Array.mem_map.mpr ⟨t.reps[i.val], Array.getElem_mem i.isLt, hi⟩

theorem cosets_invariant (t : LeftTransversal G H) (p : Element G) (x : LeftCoset H)
    (hx : x ∈ t.cosets) : (Action.leftCosets G H).act p x ∈ t.cosets := by
  obtain ⟨q, _, rfl⟩ := Array.mem_map.mp hx
  exact t.mem_cosets (p.comp q)

theorem cosets_domain (t : LeftTransversal G H) : (Action.leftCosets G H).Domain t.cosets :=
  ⟨t.distinct, fun _ j => ⟨t.cosets_invariant _ _ (Array.getElem_mem j.isLt),
    t.cosets_invariant _ _ (Array.getElem_mem j.isLt)⟩⟩

/-- Fixing every left coset is exactly membership in every ambient conjugate
of the subgroup. No normality assumption is made on the input. -/
theorem cosets_fixed (t : LeftTransversal G H) (p : Element G) :
    (∀ x ∈ t.cosets, (Action.leftCosets G H).act p x = x) ↔ Core.Member G H p.val := by
  constructor
  · intro hf g hg
    have hh := hf (LeftCoset.mk H g.inv) (t.mem_cosets ⟨g.inv, hg.inv⟩)
    change LeftCoset.mk H (p.val.comp g.inv) = LeftCoset.mk H g.inv at hh
    simpa only [Perm.inv_inv, Perm.conj] using (LeftCoset.eq_iff H _ _).mp hh
  · intro hp x hx
    obtain ⟨q, _, rfl⟩ := Array.mem_map.mp hx
    apply (LeftCoset.eq_iff H _ _).mpr
    simpa only [Perm.conj, Perm.inv_inv] using hp q.val.inv q.property.inv

end LeftTransversal

/-- The full coset action image and its kernel, retaining the exact checked
transversal used to number the cosets. -/
structure CosetAction (G H : Group n) where
  transversal : LeftTransversal G H
  image : Action.Image (Action.leftCosets G H) transversal.cosets
  kernel : Action.Kernel (Action.leftCosets G H) transversal.cosets

namespace CosetAction

variable {G H : Group n}

@[expose] def ofTransversal (t : LeftTransversal G H) : CosetAction G H where
  transversal := t
  image := ⟨t.cosets_domain, Group.ofGenerators t.cosets_domain.generators, rfl⟩
  kernel := by
    have c := Action.Kernel.fromDomain (Action.leftCosets G H) t.cosets t.cosets_domain
      t.cosets.toList (by intro x hx; simpa using hx)
    simpa only [Array.toArray_toList] using c

theorem kernel_eq_core (a : CosetAction G H) (h : H.IsSubgroup G) :
    SameGroup a.kernel.group (G.core H h) := by
  intro p
  rw [a.kernel.spec, Group.mem_core]
  constructor
  · rintro ⟨hp, hf⟩
    exact (a.transversal.cosets_fixed ⟨p, hp⟩).mp hf
  · intro hp
    have hH : Generated H.generators p := Core.Member.inside hp
    exact ⟨h p hH, (a.transversal.cosets_fixed ⟨p, h p hH⟩).mpr hp⟩

theorem map_eq_id (a : CosetAction G H) (h : H.IsSubgroup G) (p : Element G) :
    a.image.map p = Element.id a.image.group ↔ Generated (G.core H h).generators p.val := by
  rw [a.image.map_eq_id, a.transversal.cosets_fixed, G.mem_core H h]
  rfl

end CosetAction

namespace Group

/-- Reject insufficient capacity before allocating the transversal or its
action permutations. The kernel is the subgroup core in the original degree. -/
@[expose] def cosetAction (G H : Group n) (h : H.IsSubgroup G) (cap : Nat) :
    Except SizeLimit (CosetAction G H) :=
  if G.index H h ≤ cap then .ok (CosetAction.ofTransversal (G.leftTransversal H h))
  else .error ⟨G.index H h, cap⟩

theorem cosetAction_ok (G H : Group n) (h : H.IsSubgroup G) (cap : Nat) :
    (∃ a, G.cosetAction H h cap = .ok a) ↔ G.index H h ≤ cap := by
  unfold cosetAction
  split <;> simp_all

end Group

end Hex.PermGroup
