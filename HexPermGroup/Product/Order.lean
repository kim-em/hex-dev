/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.Maps
public import HexPermGroup.Enumerate

public section

namespace Hex.PermGroup.Group

/-- Unique factor decomposition gives the exact product order. The element
lists occur only in this erased proof, never in the product constructor. -/
theorem directProduct_order (G : Group n) (H : Group m) : (G.directProduct H).order = G.order * H.order := by
  let values := G.enumerate.toList.flatMap fun p => H.enumerate.toList.map (DirectProduct.pair p)
  have hn : values.Nodup := by
    apply List.pairwise_flatMap.mpr
    constructor
    · intro p _
      apply List.pairwise_map.mpr
      apply H.enumerate_nodup.imp
      intro a b hne he
      exact hne (DirectProduct.pair_injective he).2
    · apply G.enumerate_nodup.imp
      intro p q hne a ha b hb he
      obtain ⟨a', _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b', _, rfl⟩ := List.mem_map.mp hb
      exact hne (DirectProduct.pair_injective he).1
  have hm (r : Element (G.directProduct H)) : r ∈ values := by
    apply List.mem_flatMap.mpr
    refine ⟨DirectProduct.fst r, by simpa using G.mem_enumerate _, ?_⟩
    exact List.mem_map.mpr ⟨DirectProduct.snd r, by simpa using H.mem_enumerate _, DirectProduct.pair_factors r⟩
  have hl : values.length = G.order * H.order := by
    simp [values, List.length_flatMap, enumerate_size, List.map_const', List.sum_replicate_nat]
  have h₁ := List.nodup_subset_length_le hn (l₂ := (G.directProduct H).enumerate.toList)
    (fun p _ => by simpa using (G.directProduct H).mem_enumerate p)
  have h₂ := List.nodup_subset_length_le (G.directProduct H).enumerate_nodup (l₂ := values) (fun p _ => hm p)
  simp only [Array.length_toList, enumerate_size, hl] at h₁ h₂
  omega

end Hex.PermGroup.Group
