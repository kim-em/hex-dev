/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Perm

public section

namespace Hex.GraphIso.Label

/-- The raw position-to-vertex array of a typed canonical labelling. -/
@[expose] def toArray (l : Label n) : Array Nat :=
  Array.ofFn fun i : Fin n => (l.get i).val

@[simp] theorem size_toArray (l : Label n) : l.toArray.size = n := by simp [toArray]

/-- Parsing preserves the entire raw array. -/
theorem ofArray?_toArray {lab : Array Nat} {l : Label n}
    (h : ofArray? n lab = some l) : l.toArray = lab := by
  apply Array.ext ((size_toArray l).trans (ofArray?_bounds h).1.symm)
  intro i hi hi'
  have hin : i < n := by simpa only [size_toArray] using hi
  simp only [toArray, Array.getElem_ofFn]
  rw [← getElem!_pos lab i hi']
  exact ofArray?_get h i hin

/-- Every permutation array passes the executed public label parser. -/
theorem ofArray?_exists {n : Nat} {lab : Array Nat}
    (hperm : lab.toList.Perm (List.range n)) :
    ∃ l, Label.ofArray? n lab = some l := by
  have hsz : lab.size = n := by simpa using hperm.length_eq
  have hbound : ∀ v ∈ lab, v < n := by
    intro v hv
    have hm : v ∈ lab.toList := by simpa using hv
    exact List.mem_range.mp (hperm.mem_iff.mp hm)
  have hmapval : ((lab.attach.map fun v =>
      (⟨v.val, hbound v.val v.property⟩ : Fin n)).toList.map
      Fin.val) = lab.toList := by
    refine List.ext_getElem (by simp [hsz]) fun i h1 h2 => ?_
    rw [List.getElem_map, Array.getElem_toList, Array.getElem_map,
      Array.getElem_attach]
    exact (Array.getElem_toList _).symm
  have hnodupv : ((lab.attach.map fun v =>
      (⟨v.val, hbound v.val v.property⟩ : Fin n)) :
      Array (Fin n)).toList.Nodup := by
    have hmv : (((lab.attach.map fun v =>
        (⟨v.val, hbound v.val v.property⟩ : Fin n)) :
        Array (Fin n)).toList.map Fin.val).Nodup := by
      rw [hmapval]
      exact hperm.symm.nodup List.nodup_range
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hmv
    rw [List.nodup_iff_pairwise_ne]
    exact hmv.imp fun h he => h (congrArg Fin.val he)
  have hcompl : ∀ i : Fin n, i ∈ ((lab.attach.map fun v =>
      (⟨v.val, hbound v.val v.property⟩ : Fin n)) :
      Array (Fin n)).toList := by
    intro i
    have hm : i.val ∈ lab.toList :=
      hperm.mem_iff.mpr (List.mem_range.mpr i.isLt)
    rw [← hmapval] at hm
    rcases List.mem_map.mp hm with ⟨x, hx, hxe⟩
    exact (Fin.eq_of_val_eq hxe : x = i) ▸ hx
  rw [Label.ofArray?,
    dite_eq_left (⟨hsz, hbound⟩ : lab.size = n ∧ ∀ v ∈ lab, v < n)]
  rw [Label.ofVector?, Perm.ofVector?]
  rw [dite_eq_left ⟨hnodupv, hcompl⟩]
  exact ⟨_, rfl⟩

end Hex.GraphIso.Label
