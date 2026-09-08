/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Coset

public section

namespace Hex.PermGroup

/-- One representative in `G` for every left coset of `H` met by `G`, with
checked programs in the original generators of `G`. -/
structure LeftTransversal (G H : Group n) where
  reps : Array (Element G)
  distinct : (reps.map fun p => LeftCoset.mk H p.val).toList.Nodup
  covers : ∀ p : Element G, ∃ i : Fin reps.size, LeftCoset.mk H reps[i.val].val = LeftCoset.mk H p.val
  words : Vector Program reps.size
  checked : ∀ i : Fin reps.size, checkWord G.generators reps[i.val].val words[i.val] = true

namespace LeftTransversal

variable {G H : Group n}

/-- Export the representatives discovered by the left coset action. -/
@[expose] def ofOrbit (c : Action.Orbit G (LeftCoset H))
    (hc : c.Valid (Action.leftCosets G H) (LeftCoset.mk H (Perm.id n))) : LeftTransversal G H where
  reps := c.reps.toArray
  distinct := by
    have he : c.reps.toArray.map (fun p => LeftCoset.mk H p.val) = c.objects := by
      apply Array.ext
      · simp
      · intro i hi hj
        simpa [Action.leftCosets] using Action.Orbit.rep_apply hc ⟨i, hj⟩
    rw [he]
    exact hc.1.1
  covers := by
    intro p
    have hm : LeftCoset.mk H p.val ∈ c.objects :=
      (Action.Orbit.mem_iff hc _).mpr ⟨p, by simp [Action.leftCosets]⟩
    obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hm
    refine ⟨⟨i, by simpa using hi⟩, ?_⟩
    have hr := Action.Orbit.rep_apply hc ⟨i, hi⟩
    simpa [Action.leftCosets] using hr.trans he
  words := c.words.cast (by simp)
  checked := by intro i; exact (hc.2.2 ⟨i.val, by simpa using i.isLt⟩).1

theorem class_injective (t : LeftTransversal G H) {i j : Fin t.reps.size}
    (h : LeftCoset.mk H t.reps[i.val].val = LeftCoset.mk H t.reps[j.val].val) : i = j := by
  apply Fin.ext
  apply (t.distinct.getElem_inj (hi := by simp) (hj := by simp)).mp
  simpa using h

/-- The unique product of a transversal representative and a subgroup element. -/
@[expose] def product (t : LeftTransversal G H) (h : H.IsSubgroup G)
    (i : Fin t.reps.size) (p : Element H) : Element G :=
  t.reps[i.val].comp ⟨p.val, h p.val p.property⟩

@[simp] theorem product_class (t : LeftTransversal G H) (h : H.IsSubgroup G)
    (i : Fin t.reps.size) (p : Element H) :
    LeftCoset.mk H (t.product h i p).val = LeftCoset.mk H t.reps[i.val].val := by
  rw [LeftCoset.eq_iff]
  have he : t.reps[i.val].val.inv.comp (t.product h i p).val = p.val := by
    simp [product, ← Perm.comp_assoc]
  rw [he]
  exact p.property

theorem product_injective (t : LeftTransversal G H) (h : H.IsSubgroup G)
    {i j : Fin t.reps.size} {p q : Element H} (he : t.product h i p = t.product h j q) :
    i = j ∧ p = q := by
  have hc := congrArg (fun r : Element G => LeftCoset.mk H r.val) he
  simp only [product_class] at hc
  have hij := t.class_injective hc
  subst j
  refine ⟨rfl, ?_⟩
  apply Subtype.ext
  have hv := congrArg (fun r : Element G => t.reps[i.val].val.inv.comp r.val) he
  simpa [product, ← Perm.comp_assoc] using hv

theorem product_surjective (t : LeftTransversal G H) (h : H.IsSubgroup G) (p : Element G) :
    ∃ (i : Fin t.reps.size) (q : Element H), t.product h i q = p := by
  obtain ⟨i, hi⟩ := t.covers p
  let q : Element H := ⟨t.reps[i.val].val.inv.comp p.val, (LeftCoset.eq_iff H _ _).mp hi.symm⟩
  refine ⟨i, q, ?_⟩
  apply Subtype.ext
  simp [product, q, ← Perm.comp_assoc]

/-- This finite product list is used only in the erased cardinality proof;
the executable transversal builder never enumerates either group. -/
@[expose] def products (t : LeftTransversal G H) (h : H.IsSubgroup G) : List (Element G) :=
  (List.finRange t.reps.size).flatMap fun i => H.enumerate.toList.map (t.product h i)

theorem products_nodup (t : LeftTransversal G H) (h : H.IsSubgroup G) : (t.products h).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    apply List.pairwise_map.mpr
    apply H.enumerate_nodup.imp
    intro p q hne he
    exact hne (t.product_injective h he).2
  · apply (List.nodup_finRange t.reps.size).imp
    intro i j hne p hp q hq he
    obtain ⟨p', _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨q', _, rfl⟩ := List.mem_map.mp hq
    exact hne (t.product_injective h he).1

theorem mem_products (t : LeftTransversal G H) (h : H.IsSubgroup G) (p : Element G) :
    p ∈ t.products h := by
  obtain ⟨i, q, he⟩ := t.product_surjective h p
  simp only [products, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  exact ⟨i, q, by simpa using H.mem_enumerate q, he⟩

theorem products_length (t : LeftTransversal G H) (h : H.IsSubgroup G) :
    (t.products h).length = t.reps.size * H.order := by
  simp [products, List.length_flatMap, Group.enumerate_size, List.map_const', List.sum_replicate_nat]

/-- Lagrange's formula for the verified transversal, using exact naturals. -/
theorem order_eq (t : LeftTransversal G H) (h : H.IsSubgroup G) : G.order = t.reps.size * H.order := by
  have h₁ := List.nodup_subset_length_le (t.products_nodup h) (l₂ := G.enumerate.toList)
    (fun p _ => by simpa using G.mem_enumerate p)
  have h₂ := List.nodup_subset_length_le G.enumerate_nodup (l₂ := t.products h)
    (fun p _ => t.mem_products h p)
  rw [t.products_length h] at h₁ h₂
  simp only [Array.length_toList, Group.enumerate_size] at h₁ h₂
  omega

end LeftTransversal

end Hex.PermGroup
