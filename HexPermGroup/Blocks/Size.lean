/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Blocks
public import HexPermGroup.Predicates

public section

namespace Hex.PermGroup.Partition

/-- Number of points in the block through a point, including that point. -/
@[expose] def blockSize (p : Partition n) (x : Fin n) : Nat :=
  (List.finRange n).countP fun y => decide (p.Same x y)

theorem blockSize_pos (p : Partition n) (x : Fin n) : 0 < p.blockSize x := by
  apply List.countP_pos_iff.mpr
  exact ⟨x, by simp, by simp [Same]⟩

/-- Group elements biject the points in a block with the points in its image. -/
theorem blockSize_image (p : Partition n) {G : Group n} (hp : p.IsInvariant G)
    {g : Perm n} (hg : Generated G.generators g) (x : Fin n) :
    p.blockSize x = p.blockSize (g.get x) := by
  have hn : ((List.finRange n).map g.get).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    apply (List.nodup_finRange n).imp
    intro x y hxy he
    exact hxy (g.get_inj he)
  have he : ((List.finRange n).map g.get).Perm (List.finRange n) := by
    apply (List.perm_ext_iff_of_nodup hn (List.nodup_finRange n)).mpr
    intro y
    simp only [List.mem_map, List.mem_finRange, true_and, iff_true]
    exact g.get_surj y
  have hc := he.countP_eq (fun y => decide (p.Same (g.get x) y))
  simp only [List.countP_map, Function.comp_def] at hc
  have hf : (fun y => decide (p.Same (g.get x) (g.get y))) =
      (fun y => decide (p.Same x y)) := by
    funext y
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (hp g hg x y).symm
  rw [hf] at hc
  exact hc

/-- Equal block sizes require transitivity; invariant partitions of an
intransitive action can have unequal block sizes. -/
theorem blockSize_eq (p : Partition n) {G : Group n} (hp : p.IsInvariant G)
    (ht : G.isTransitive = true) (x y : Fin n) : p.blockSize x = p.blockSize y := by
  obtain ⟨g, hg, he⟩ := (G.isTransitive_iff.mp ht).2 x y
  simpa only [he] using p.blockSize_image hp hg x

end Hex.PermGroup.Partition
