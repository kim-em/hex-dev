/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Action.Image
public import HexPermGroup.Action.Kernel
public import HexPermGroup.Partition
public import HexPermGroupMathlib.Group
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace Hex.PermGroup.Action

variable {G : Group n} {α : Type u}

/-- Interpret the executable action as a Mathlib action, preserving its values. -/
@[expose, instance_reducible] def toMulAction (a : Action G α) : MulAction (Element G) α where
  smul := a.act
  one_smul := a.id_act
  mul_smul := a.comp_act

@[simp] theorem smul_spec (a : Action G α) (p : Element G) (x : α) :
    let _ := a.toMulAction
    p • x = a.act p x := rfl

namespace Image

variable [DecidableEq α] {a : Action G α} {objects : Array α} (image : Image a objects)

/-- The checked image map is a surjective group homomorphism. -/
@[expose] def hom : Element G →* Element image.group where
  toFun := image.map
  map_one' := image.map_id
  map_mul' := image.map_comp

theorem hom_surjective : Function.Surjective image.hom := image.map_surjective

theorem mem_ker (p : Element G) : p ∈ image.hom.ker ↔
    ∀ x ∈ objects, a.act p x = x := image.map_eq_id p

/-- The image subgroup is exactly Mathlib's image of the induced action. -/
theorem contains_spec (q : Perm objects.size) :
    q.toEquiv ∈ closure image.group.generators ↔
      ∃ p : Element G, (image.domain.perm p).toEquiv = q.toEquiv := by
  rw [← image.group.contains_spec, image.contains_iff]
  constructor <;> rintro ⟨p, hp⟩
  · exact ⟨p, congrArg Perm.toEquiv hp⟩
  · exact ⟨p, by simpa using congrArg Perm.ofEquiv hp⟩

/-- The finite homomorphism theorem identifies the exact image order even for
nonfaithful actions. The kernel here fixes every recorded domain object. -/
theorem order_eq : G.order = Nat.card image.hom.ker * image.group.order := by
  have hc (H : Group n) : Nat.card (Element H) = H.order :=
    (Nat.card_congr (Element.equiv H).toEquiv).trans H.order_card.symm
  have hi : Nat.card (Element image.group) = image.group.order :=
    (Nat.card_congr (Element.equiv image.group).toEquiv).trans image.group.order_card.symm
  have he := image.hom.ker.card_mul_index
  rw [Subgroup.index_ker, image.hom.range_eq_top_of_surjective image.hom_surjective] at he
  simpa only [Subgroup.card_top, hc, hi] using he.symm

theorem injective_iff : Function.Injective image.hom ↔
    ∀ p : Element G, (∀ x ∈ objects, a.act p x = x) → p = Element.id G := by
  constructor
  · intro hi p hp
    apply hi
    change image.map p = image.map (Element.id G)
    rw [image.map_id]
    exact (image.map_eq_id p).mpr hp
  · intro h
    apply image.hom.ker_eq_bot_iff.mp
    apply le_antisymm _ bot_le
    intro p hp
    exact Subgroup.mem_bot.mpr (h p ((image.mem_ker p).mp hp))

end Image

namespace Orbit

variable [DecidableEq α] {a : Action G α} {x : α} {c : Orbit G α} (h : c.Valid a x)

include h in
omit [DecidableEq α] in
theorem mem_spec (y : α) :
    let _ := a.toMulAction
    y ∈ c.objects ↔ y ∈ MulAction.orbit (Element G) x := by
  let _ := a.toMulAction
  exact (mem_iff h y).trans MulAction.mem_orbit_iff.symm

theorem stabilizer_spec (p : Element G) :
    let _ := a.toMulAction
    p.val.toEquiv ∈ closure (stabilizer h).generators ↔ p ∈ MulAction.stabilizer (Element G) x := by
  change p.val.toEquiv ∈ closure (stabilizer h).generators ↔ a.act p x = x
  rw [← generated_iff_mem, mem_stabilizer]
  exact ⟨fun ⟨_, he⟩ => he, fun he => ⟨p.property, he⟩⟩

end Orbit

namespace Kernel

variable [DecidableEq α] {a : Action G α} {objects : Array α}
  (kernel : Kernel a objects) (image : Image a objects)

/-- The computed common stabilizer is exactly the kernel of the image map. -/
@[expose] def equiv : Element kernel.group ≃ image.hom.ker where
  toFun p := ⟨⟨p.val, kernel.subgroup p.val p.property⟩,
    (image.mem_ker _).mpr ((kernel.spec p.val).mp p.property).choose_spec⟩
  invFun p := ⟨p.val.val, (kernel.spec p.val.val).mpr
    ⟨p.val.property, (image.mem_ker p.val).mp p.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_ker : Nat.card image.hom.ker = kernel.group.order :=
  (Nat.card_congr (kernel.equiv image).symm).trans
    ((Nat.card_congr (Element.equiv kernel.group).toEquiv).trans kernel.group.order_card.symm)

/-- Exact order factorization for the two executable constructions. -/
theorem order_mul_image : G.order = kernel.group.order * image.group.order := by
  rw [image.order_eq, kernel.card_ker image]

theorem injective_iff : Function.Injective image.hom ↔ kernel.group.order = 1 := by
  rw [← image.hom.ker_eq_bot_iff, Subgroup.eq_bot_iff_card, kernel.card_ker image]

end Kernel

end Hex.PermGroup.Action

namespace Hex.PermGroup.Partition

/-- Canonical block labels encode an equivalence relation on all points. -/
@[expose, instance_reducible] def toSetoid (p : Partition n) : Setoid (Fin n) where
  r := p.Same
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

theorem toSetoid_injective : Function.Injective (toSetoid (n := n)) := by
  intro p q he
  apply Partition.ext
  intro x y
  exact Iff.of_eq (congrArg (fun s : Setoid (Fin n) => s.r x y) he)

theorem permute_spec (s : Perm n) (p : Partition n) (x y : Fin n) :
    (p.permute s).toSetoid.r x y ↔ p.toSetoid.r (s.toEquiv.symm x) (s.toEquiv.symm y) :=
  p.permute_same s x y

end Hex.PermGroup.Partition
