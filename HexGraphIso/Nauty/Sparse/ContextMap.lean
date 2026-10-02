/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.NativeCounts
public import HexGraphIso.Nauty.Spec.SpecIso

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A native graph isomorphism transports the proof interpretation of its
rows. This changes no graph representation in the executable. -/
theorem Graph.context_map (G H : Hex.SparseGraph n) (p : Perm n)
    (h : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v) :
    RowsMap (renamingOf p) (Graph.context G).g (Graph.context H).g := by
  refine ⟨by simp [Graph.context], by simp [Graph.context], fun v hv => ?_⟩
  have hσv := ((renamingOf p).maps v).mp hv
  apply VSet.ext
  intro t
  by_cases ht : t < n
  · obtain ⟨w, hw⟩ := p.get_surj ⟨t, ht⟩
    have hσw : renamingOf p w.val = t := by
      rw [renamingOf_lt p w.isLt]
      exact congrArg Fin.val hw
    rw [← hσw, VSet.mem_image_apply (renamingOf p) _ w.isLt,
      Graph.context_mem H ⟨renamingOf p v, hσv⟩ ⟨renamingOf p w.val, (renamingOf p).maps _ |>.mp w.isLt⟩,
      Graph.context_mem G ⟨v, hv⟩ w]
    have hv' : (⟨renamingOf p v, hσv⟩ : Fin n) = p.get ⟨v, hv⟩ := Fin.ext (renamingOf_lt p hv)
    have hw' : (⟨renamingOf p w.val, (renamingOf p).maps _ |>.mp w.isLt⟩ : Fin n) = p.get w :=
      Fin.ext (renamingOf_lt p w.isLt)
    rw [hv', hw']
    exact h _ _
  · rw [VSet.mem_of_ge (by omega), VSet.mem_of_ge (by omega)]

/-- Applying the vertex permutation to every raw label entry preserves
the label-permutation contract. -/
theorem perm_map {lab : Array Nat} (hp : lab.toList.Perm (List.range n)) (p : Perm n) :
    (lab.map (renamingOf p).toFun).toList.Perm (List.range n) := by
  rw [Array.toList_map]
  apply (List.perm_ext_iff_of_nodup
    ((hp.nodup_iff.mpr List.nodup_range).map _ (fun _ _ hn he => hn ((renamingOf p).inj _ _ he)))
    List.nodup_range).mpr
  intro v
  constructor
  · intro hm
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
    exact List.mem_range.mpr (((renamingOf p).maps u).mp (List.mem_range.mp (hp.mem_iff.mp hu)))
  · intro hv
    have hv := List.mem_range.mp hv
    obtain ⟨u, hu⟩ := p.get_surj ⟨v, hv⟩
    apply List.mem_map.mpr
    refine ⟨u.val, hp.mem_iff.mpr (List.mem_range.mpr u.isLt), ?_⟩
    exact (renamingOf_lt p u.isLt).trans (congrArg Fin.val hu)

end Hex.GraphIso.Nauty.Sparse
