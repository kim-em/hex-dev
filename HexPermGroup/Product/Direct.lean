/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.Projection
public import HexPermGroup.Build

public section

namespace Hex.PermGroup.Group

/-- Direct product on consecutive disjoint supports, retaining all fixed
points and allowing either declared factor degree to be zero. -/
@[expose] def directProduct (G : Group n) (H : Group m) : Group (n + m) :=
  ofGenerators ((G.generators.map fun p => p.sum (Perm.id m)) ++
    (H.generators.map fun q => (Perm.id n).sum q))

theorem direct_left_mem (G : Group n) (H : Group m) (p : Perm n) (hp : Generated G.generators p) :
    Generated (G.directProduct H).generators (p.sum (Perm.id m)) := by
  apply hp.lift
  · simpa only [Perm.sum_id] using (Generated.id (S := (G.directProduct H).generators))
  · intro p hp
    exact .generator (Array.mem_append.mpr (Or.inl (Array.mem_map.mpr ⟨p, hp, rfl⟩)))
  · intro p q hp hq
    simpa only [← Perm.sum_comp, Perm.comp_id] using hp.comp hq
  · intro p hp
    simpa only [← Perm.sum_inv, Perm.inv_id] using hp.inv

theorem direct_right_mem (G : Group n) (H : Group m) (q : Perm m) (hq : Generated H.generators q) :
    Generated (G.directProduct H).generators ((Perm.id n).sum q) := by
  apply hq.lift
  · simpa only [Perm.sum_id] using (Generated.id (S := (G.directProduct H).generators))
  · intro q hq
    exact .generator (Array.mem_append.mpr (Or.inr (Array.mem_map.mpr ⟨q, hq, rfl⟩)))
  · intro p q hp hq
    simpa only [← Perm.sum_comp, Perm.comp_id] using hp.comp hq
  · intro p hp
    simpa only [← Perm.sum_inv, Perm.inv_id] using hp.inv

theorem direct_sum_mem (G : Group n) (H : Group m) (p : Perm n) (q : Perm m)
    (hp : Generated G.generators p) (hq : Generated H.generators q) :
    Generated (G.directProduct H).generators (p.sum q) := by
  simpa only [← Perm.sum_comp, Perm.comp_id, Perm.id_comp] using
    (G.direct_left_mem H p hp).comp (G.direct_right_mem H q hq)

/-- Every generated product element has a factor decomposition; the converse
proves that the two embedded factor images generate the full output. -/
theorem mem_directProduct (G : Group n) (H : Group m) (r : Perm (n + m)) :
    Generated (G.directProduct H).generators r ↔
      ∃ (p : Perm n) (q : Perm m), Generated G.generators p ∧ Generated H.generators q ∧ r = p.sum q := by
  constructor
  · intro hr
    apply hr.lift
    · exact ⟨Perm.id n, Perm.id m, .id, .id, Perm.sum_id.symm⟩
    · intro r hr
      simp only [directProduct, generators_ofGenerators, Array.mem_append] at hr
      rcases hr with hr | hr
      · obtain ⟨p, hp, rfl⟩ := Array.mem_map.mp hr
        exact ⟨p, Perm.id m, .generator hp, .id, rfl⟩
      · obtain ⟨q, hq, rfl⟩ := Array.mem_map.mp hr
        exact ⟨Perm.id n, q, .id, .generator hq, rfl⟩
    · rintro r s ⟨p, q, hp, hq, rfl⟩ ⟨a, b, ha, hb, rfl⟩
      exact ⟨p.comp a, q.comp b, hp.comp ha, hq.comp hb, (Perm.sum_comp ..).symm⟩
    · rintro r ⟨p, q, hp, hq, rfl⟩
      exact ⟨p.inv, q.inv, hp.inv, hq.inv, (Perm.sum_inv ..).symm⟩
  · rintro ⟨p, q, hp, hq, rfl⟩
    exact G.direct_sum_mem H p q hp hq

end Hex.PermGroup.Group

namespace Hex.PermGroup.DirectProduct

variable {G : Group n} {H : Group m}

/-- The pair embedding is a bijection onto the constructed product group. -/
@[expose] def pair (p : Element G) (q : Element H) : Element (G.directProduct H) :=
  ⟨p.val.sum q.val, G.direct_sum_mem H p.val q.val p.property q.property⟩

theorem factors (r : Element (G.directProduct H)) : ∃ (p : Perm n) (q : Perm m), r.val = p.sum q := by
  obtain ⟨p, q, _, _, he⟩ := (G.mem_directProduct H r.val).mp r.property
  exact ⟨p, q, he⟩

@[expose] def fst (r : Element (G.directProduct H)) : Element G :=
  ⟨Perm.Sum.left r.val (factors r), by
    obtain ⟨p, q, hp, _, he⟩ := (G.mem_directProduct H r.val).mp r.property
    simpa only [he, Perm.Sum.left_sum] using hp⟩

@[expose] def snd (r : Element (G.directProduct H)) : Element H :=
  ⟨Perm.Sum.right r.val (factors r), by
    obtain ⟨p, q, _, hq, he⟩ := (G.mem_directProduct H r.val).mp r.property
    simpa only [he, Perm.Sum.right_sum] using hq⟩

@[simp] theorem fst_pair (p : Element G) (q : Element H) : fst (pair p q) = p := by
  apply Subtype.ext
  exact Perm.Sum.left_sum ..

@[simp] theorem snd_pair (p : Element G) (q : Element H) : snd (pair p q) = q := by
  apply Subtype.ext
  exact Perm.Sum.right_sum ..

@[simp] theorem pair_factors (r : Element (G.directProduct H)) : pair (fst r) (snd r) = r := by
  apply Subtype.ext
  exact Perm.Sum.reconstruct ..

theorem pair_injective {p a : Element G} {q b : Element H} (h : pair p q = pair a b) : p = a ∧ q = b :=
  ⟨by simpa only [fst_pair] using congrArg fst h, by simpa only [snd_pair] using congrArg snd h⟩

theorem pair_comp (p a : Element G) (q b : Element H) :
    pair (p.comp a) (q.comp b) = (pair p q).comp (pair a b) :=
  Subtype.ext (Perm.sum_comp ..)

@[simp] theorem pair_id : pair (Element.id G) (Element.id H) = Element.id (G.directProduct H) :=
  Subtype.ext Perm.sum_id

theorem fst_comp (r s : Element (G.directProduct H)) : fst (r.comp s) = (fst r).comp (fst s) := by
  have h := congrArg fst (pair_comp (fst r) (fst s) (snd r) (snd s))
  simpa only [fst_pair, pair_factors] using h.symm

theorem snd_comp (r s : Element (G.directProduct H)) : snd (r.comp s) = (snd r).comp (snd s) := by
  have h := congrArg snd (pair_comp (fst r) (fst s) (snd r) (snd s))
  simpa only [snd_pair, pair_factors] using h.symm

end Hex.PermGroup.DirectProduct
