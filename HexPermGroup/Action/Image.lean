/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Action.Domain
public import HexPermGroup.Enumerate

public section

namespace Hex.PermGroup.Action

variable {G : Group n} {α : Type u} [DecidableEq α] {a : Action G α} {objects : Array α}

namespace Domain

/-- Images of the original generators, in their original order. -/
@[expose] def generators (h : a.Domain objects) : Array (Perm objects.size) :=
  (Hex.Vector.ofFn' fun i : Fin G.generators.size =>
    h.perm ⟨G.generators[i.val], .generator (Array.getElem_mem i.isLt)⟩).toArray

@[simp] theorem generators_size (h : a.Domain objects) : h.generators.size = G.generators.size := by
  simp [generators]

theorem mem_generators (h : a.Domain objects) (q : Perm objects.size) :
    q ∈ h.generators ↔ ∃ i : Fin G.generators.size,
      h.perm ⟨G.generators[i.val], .generator (Array.getElem_mem i.isLt)⟩ = q := by
  simp only [generators, Array.mem_iff_getElem, Vector.size_toArray,
    Vector.getElem_toArray, Hex.Vector.getElem_ofFn']
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨⟨i, hi⟩, he⟩
  · rintro ⟨i, he⟩
    exact ⟨i.val, i.isLt, he⟩

/-- The generated image is exactly the image of all original group elements;
no faithfulness assumption is needed. -/
theorem generated_iff (h : a.Domain objects) (q : Perm objects.size) :
    Generated h.generators q ↔ ∃ p : Element G, h.perm p = q := by
  constructor
  · intro hq
    apply hq.lift
    · exact ⟨Element.id G, h.perm_id⟩
    · intro r hr
      obtain ⟨i, hi⟩ := (h.mem_generators r).mp hr
      exact ⟨⟨G.generators[i.val], .generator (Array.getElem_mem i.isLt)⟩, hi⟩
    · rintro r s ⟨p, rfl⟩ ⟨q, rfl⟩
      exact ⟨p.comp q, h.perm_comp p q⟩
    · rintro r ⟨p, rfl⟩
      exact ⟨p.inv, h.perm_inv p⟩
  · rintro ⟨⟨p, hp⟩, rfl⟩
    induction hp with
    | id =>
      change Generated h.generators (h.perm (Element.id G))
      rw [perm_id]
      exact .id
    | generator hp =>
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hp
      exact .generator ((h.mem_generators _).mpr ⟨⟨i, hi⟩, rfl⟩)
    | @comp p q hp hq ihp ihq =>
      change Generated h.generators (h.perm (Element.comp ⟨p, hp⟩ ⟨q, hq⟩))
      rw [perm_comp]
      exact .comp ihp ihq
    | @inv p hp ih =>
      change Generated h.generators (h.perm (Element.inv ⟨p, hp⟩))
      rw [perm_inv]
      exact .inv ih

end Domain

/-- A checked image group, tied to the supplied domain enumeration and retaining
the order of the original generators for preimage certificates. -/
structure Image (a : Action G α) (objects : Array α) where
  domain : a.Domain objects
  group : Group objects.size
  generators_eq : group.generators = domain.generators

namespace Image

variable (image : Image a objects)

/-- The permutation induced by an original group element belongs to the image. -/
@[expose] def map (p : Element G) : Element image.group :=
  ⟨image.domain.perm p, by
    rw [image.generators_eq]
    exact (image.domain.generated_iff _).mpr ⟨p, rfl⟩⟩

@[simp] theorem map_id : image.map (Element.id G) = Element.id image.group := by
  apply Subtype.ext
  exact image.domain.perm_id

theorem map_comp (p q : Element G) : image.map (p.comp q) = (image.map p).comp (image.map q) := by
  apply Subtype.ext
  exact image.domain.perm_comp p q

theorem map_surjective (q : Element image.group) : ∃ p : Element G, image.map p = q := by
  have hq : Generated image.domain.generators q.val := by
    simpa only [image.generators_eq] using q.property
  rw [image.domain.generated_iff] at hq
  obtain ⟨p, hp⟩ := hq
  exact ⟨p, Subtype.ext hp⟩

theorem contains_iff (q : Perm objects.size) : image.group.contains q = true ↔
    ∃ p : Element G, image.domain.perm p = q := by
  rw [Group.contains_iff, image.generators_eq, Domain.generated_iff]

/-- The source generator associated with an image generator. -/
@[expose] def source (i : Fin image.group.generators.size) : Fin G.generators.size :=
  ⟨i.val, by simpa [image.generators_eq] using i.isLt⟩

@[expose] def preimage (i : Fin image.group.generators.size) : Element G :=
  ⟨G.generators[(image.source i).val], .generator (Array.getElem_mem (image.source i).isLt)⟩

@[expose] def preimageWord (i : Fin image.group.generators.size) : Program :=
  ⟨#[.generator (image.source i).val], 0⟩

theorem check_preimage (i : Fin image.group.generators.size) :
    checkWord G.generators (image.preimage i).val (image.preimageWord i) = true := by
  simp [preimageWord, preimage, checkWord, Program.eval, Program.evalCertified,
    Program.evalNodes, Program.evalNode, (image.source i).isLt]

theorem map_preimage (i : Fin image.group.generators.size) :
    (image.map (image.preimage i)).val = image.group.generators[i.val] := by
  simp [map, preimage, source, image.generators_eq, Domain.generators]

theorem map_eq_id (p : Element G) : image.map p = Element.id image.group ↔
    ∀ x ∈ objects, a.act p x = x := by
  rw [Subtype.ext_iff]
  exact image.domain.perm_eq_id p

end Image

inductive ImageError where
  | sizeLimit (limit : SizeLimit)
  | invalidDomain
  deriving DecidableEq, Repr

/-- Check the explicit allocation bound and signed generator closure before
constructing index permutations or an image chain. The empty domain is valid. -/
@[expose] def actionImage (a : Action G α) (cap : Nat) (objects : Array α) :
    Except ImageError (Image a objects) :=
  if objects.size ≤ cap then
    if h : a.Domain objects then
      .ok ⟨h, Group.ofGenerators h.generators, rfl⟩
    else .error .invalidDomain
  else .error (.sizeLimit ⟨objects.size, cap⟩)

theorem actionImage_ok (a : Action G α) (cap : Nat) (objects : Array α) :
    (∃ image, a.actionImage cap objects = .ok image) ↔ objects.size ≤ cap ∧ a.Domain objects := by
  unfold actionImage
  split <;> rename_i hc
  · split <;> simp_all
  · simp_all
    omega

theorem actionImage_sizeLimit (a : Action G α) (cap : Nat) (objects : Array α)
    (h : cap < objects.size) :
    a.actionImage cap objects = .error (.sizeLimit ⟨objects.size, cap⟩) := by
  simp [actionImage, Nat.not_le.mpr h]

end Hex.PermGroup.Action
