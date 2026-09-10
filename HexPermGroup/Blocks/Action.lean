/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Blocks
public import HexPermGroup.Action.Kernel

public section

namespace Hex.PermGroup

namespace Partition

/-- A block is identified by its least point. -/
abbrev Block (p : Partition n) := {x : Fin n // p.labels[x.val] = x}

/-- The block containing a point. -/
@[expose] def block (p : Partition n) (x : Fin n) : p.Block := ⟨p.labels[x.val], p.idem x⟩

theorem block_eq (p : Partition n) (x y : Fin n) : p.block x = p.block y ↔ p.Same x y :=
  Subtype.ext_iff

/-- Canonical block order is increasing least-point order. -/
@[expose] def blocks (p : Partition n) : Array p.Block :=
  (p.roots.attach.map fun x => ⟨x.val, (p.mem_roots x.val).mp x.property⟩).toArray

@[simp] theorem blocks_size (p : Partition n) : p.blocks.size = p.roots.length := by
  simp [blocks]

theorem mem_blocks (p : Partition n) (b : p.Block) : b ∈ p.blocks := by
  apply List.mem_toArray.mpr
  apply List.mem_map.mpr
  exact ⟨⟨b.val, (p.mem_roots b.val).mpr b.property⟩, by simp, rfl⟩

theorem blocks_nodup (p : Partition n) : p.blocks.toList.Nodup := by
  refine List.pairwise_iff_getElem.mpr fun i j hi hj hij he => ?_
  have hr := (List.pairwise_iff_getElem.mp p.roots_nodup) i j
    (by simpa [blocks] using hi) (by simpa [blocks] using hj) hij
  exact hr (by simpa [blocks] using congrArg Subtype.val he)

end Partition

namespace Action

/-- The action on least-point block representatives. Invariance is required;
transitivity and equal block sizes are not. -/
@[expose] def blocks (G : Group n) (p : Partition n) (hp : p.IsInvariant G) : Action G p.Block where
  act g b := p.block (g.val.get b.val)
  id_act b := by
    apply Subtype.ext
    simp only [Partition.block, Element.val_id, Perm.get_id]
    exact b.property
  comp_act g h b := by
    apply Subtype.ext
    simp only [Partition.block, Element.val_comp, Perm.get_comp]
    exact (hp g.val g.property _ _).mp (p.idem (h.val.get b.val)).symm

theorem blocks_image (G : Group n) (p : Partition n) (hp : p.IsInvariant G)
    (g : Element G) (x : Fin n) :
    (blocks G p hp).act g (p.block x) = p.block (g.val.get x) := by
  apply Subtype.ext
  exact ((hp g.val g.property x p.labels[x.val]).mp (p.idem x).symm).symm

theorem blocks_domain (G : Group n) (p : Partition n) (hp : p.IsInvariant G) :
    (blocks G p hp).Domain p.blocks :=
  ⟨p.blocks_nodup, fun _ _ => ⟨p.mem_blocks _, p.mem_blocks _⟩⟩

/-- Fixing each block permits arbitrary permutations within that block. -/
theorem blocks_fixed (G : Group n) (p : Partition n) (hp : p.IsInvariant G) (g : Element G) :
    (∀ b ∈ p.blocks, (blocks G p hp).act g b = b) ↔ ∀ x, p.Same (g.val.get x) x := by
  constructor
  · intro h x
    have he := h (p.block x) (p.mem_blocks _)
    rw [blocks_image] at he
    exact (p.block_eq _ _).mp he
  · intro h b _
    apply Subtype.ext
    exact (h b.val).trans b.property

end Action

/-- The induced permutation image on canonically numbered blocks, together
with its exact kernel in the original action degree. -/
structure BlockAction (G : Group n) (p : Partition n) (hp : p.IsInvariant G) where
  image : Action.Image (Action.blocks G p hp) p.blocks
  kernel : Action.Kernel (Action.blocks G p hp) p.blocks

namespace BlockAction

variable {G : Group n} {p : Partition n} {hp : p.IsInvariant G}

theorem mem_kernel (a : BlockAction G p hp) (g : Perm n) :
    Generated a.kernel.group.generators g ↔
      Generated G.generators g ∧ ∀ x, p.Same (g.get x) x := by
  rw [a.kernel.spec]
  constructor
  · rintro ⟨hg, hf⟩
    exact ⟨hg, (Action.blocks_fixed G p hp ⟨g, hg⟩).mp hf⟩
  · rintro ⟨hg, hf⟩
    exact ⟨hg, (Action.blocks_fixed G p hp ⟨g, hg⟩).mpr hf⟩

/-- The image map uses the recorded canonical block numbering. -/
theorem map_block (a : BlockAction G p hp) (g : Element G) (i : Fin p.blocks.size) :
    p.blocks[((a.image.map g).val.get i).val] = p.block (g.val.get p.blocks[i.val].val) := by
  simpa only [Action.Image.map, Action.Domain.get_perm, Action.blocks] using
    a.image.domain.object_act g i

end BlockAction

namespace Group

/-- Construct the full image and kernel after checking the block-count budget.
The domain consists of all blocks, including fixed blocks and unequal sizes. -/
@[expose] def blockAction (G : Group n) (p : Partition n) (hp : p.IsInvariant G) (cap : Nat) :
    Except Action.ImageError (BlockAction G p hp) := do
  let image ← (Action.blocks G p hp).actionImage cap p.blocks
  let kernel ← (Action.blocks G p hp).actionKernel cap p.blocks
  return ⟨image, kernel⟩

theorem blockAction_ok (G : Group n) (p : Partition n) (hp : p.IsInvariant G) (cap : Nat) :
    (∃ a, G.blockAction p hp cap = .ok a) ↔ p.roots.length ≤ cap := by
  rw [← p.blocks_size]
  unfold blockAction
  by_cases hc : p.blocks.size ≤ cap
  · obtain ⟨image, hi⟩ := ((Action.blocks G p hp).actionImage_ok cap p.blocks).mpr
      ⟨hc, Action.blocks_domain G p hp⟩
    obtain ⟨kernel, hk⟩ := ((Action.blocks G p hp).actionKernel_ok cap p.blocks).mpr
      ⟨hc, Action.blocks_domain G p hp⟩
    simp only [hi, hk]
    exact ⟨fun _ => hc, fun _ => ⟨⟨image, kernel⟩, rfl⟩⟩
  · have hi := (Action.blocks G p hp).actionImage_sizeLimit cap p.blocks (Nat.lt_of_not_ge hc)
    simp only [hi]
    constructor
    · rintro ⟨_, h⟩
      cases h
    · exact fun h => False.elim (hc h)

end Group

end Hex.PermGroup
