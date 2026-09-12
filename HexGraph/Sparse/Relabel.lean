/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraph.Sparse.Normalize
public import HexGraph.Sparse.Pack
public import HexPermGroup.Perm

public section

namespace Hex.SparseGraph

variable {n : Nat}

/-- Relabel by the bijection from new vertices to old vertices. Neighbours
are mapped by its inverse and sorted, without a dense adjacency matrix. -/
@[expose] def relabel (G : SparseGraph n) (p : Perm n) : SparseGraph n :=
  let q := p.inv
  let rows := Vector.ofFn fun i =>
    Builder.mapRow (G.nbrs (p.get i)) q.get
  ofRows rows
    (fun i => by simp [rows, Builder.mapRow, Builder.sorted_normalize])
    (fun i j => by
      simp only [rows, Builder.mapRow, Fin.getElem_fin, Vector.getElem_ofFn, Builder.mem_normalize,
        List.mem_map, Array.mem_toList_iff]
      constructor
      · rintro ⟨v, hv, he⟩
        have hvj : v = p.get j := by rw [← he, Perm.get_inv_get]
        refine ⟨p.get i, ?_, Perm.inv_get_get p i⟩
        rw [hvj] at hv
        exact (G.symm (p.get i) (p.get j)).mp hv
      · rintro ⟨v, hv, he⟩
        have hvi : v = p.get i := by rw [← he, Perm.get_inv_get]
        refine ⟨p.get j, ?_, Perm.inv_get_get p j⟩
        rw [hvi] at hv
        exact (G.symm (p.get j) (p.get i)).mp hv)
    (fun i => by
      simp only [rows, Builder.mapRow, Fin.getElem_fin, Vector.getElem_ofFn, Builder.mem_normalize,
        List.mem_map, Array.mem_toList_iff]
      rintro ⟨v, hv, he⟩
      have hvi : v = p.get i := by rw [← he, Perm.get_inv_get]
      rw [hvi] at hv
      exact G.loopless (p.get i) hv)

@[simp] theorem adj_relabel (G : SparseGraph n) (p : Perm n) (i j : Fin n) :
    (G.relabel p).adj i j = G.adj (p.get i) (p.get j) := by
  rw [Bool.eq_iff_iff, ← mem_nbrs, ← mem_nbrs, ← Array.mem_toList_iff,
    relabel, nbrs_ofRows]
  simp only [Builder.mapRow, Fin.getElem_fin, Vector.getElem_ofFn, Builder.mem_normalize,
    List.mem_map, Array.mem_toList_iff]
  constructor
  · rintro ⟨v, hv, he⟩
    have hvj : v = p.get j := by rw [← he, Perm.get_inv_get]
    exact hvj ▸ hv
  · intro h
    exact ⟨p.get j, h, Perm.inv_get_get p j⟩

/-- Row normalization changes only the order of the mapped neighbours. -/
theorem nbrs_relabel_perm (G : SparseGraph n) (p : Perm n) (i : Fin n) :
    ((G.relabel p).nbrs i).toList.Perm ((G.nbrs (p.get i)).toList.map p.inv.get) := by
  apply (List.perm_ext_iff_of_nodup
    (((G.relabel p).sorted i).imp fun h => Fin.ne_of_lt h)
    ((G.sorted (p.get i)).map p.inv.get
      (fun _ _ h he => Fin.ne_of_lt h (p.inv.get_inj he)))).mpr
  intro v
  change v ∈ ((G.relabel p).nbrs i).toList ↔ v ∈ (G.nbrs (p.get i)).toList.map p.inv.get
  rw [Array.mem_toList_iff, mem_nbrs, adj_relabel]
  simp only [List.mem_map]
  constructor
  · intro h
    exact ⟨p.get v, Array.mem_toList_iff.mpr ((mem_nbrs G _ _).mpr h), Perm.inv_get_get p v⟩
  · rintro ⟨w, hw, he⟩
    have hwv : w = p.get v := by rw [← he, Perm.get_inv_get]
    rw [hwv] at hw
    exact (mem_nbrs G _ _).mp (Array.mem_toList_iff.mp hw)

@[simp] theorem degree_relabel (G : SparseGraph n) (p : Perm n) (i : Fin n) :
    (G.relabel p).degree i = G.degree (p.get i) := by
  simpa only [degree_eq_size, Array.length_toList, List.length_map] using
    (nbrs_relabel_perm G p i).length_eq

/-- The packed storage length is the sum of the row lengths. -/
theorem neighbors_size_eq (G : SparseGraph n) :
    G.neighbors.size = (List.ofFn G.degree).sum := by
  obtain ⟨rows, hlen, ho, hn⟩ := G.layout
  have hr : rows.map List.length = List.ofFn G.degree := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      have hib : i < n := by simpa using hj
      simp only [List.getElem_map, List.getElem_ofFn, degree_eq_size]
      have he : (G.nbrs ⟨i, hib⟩).toList = rows[i]'(by omega) := by
        simp only [nbrs, ho, hn]
        exact row_pack rows i (by omega)
      simpa only [Array.length_toList] using (congrArg List.length he).symm
  rw [hn, List.size_toArray, List.length_flatten, hr]

/-- Relabelling preserves the allocation needed for packed adjacency. -/
@[simp] theorem neighbors_size_relabel (G : SparseGraph n) (p : Perm n) :
    (G.relabel p).neighbors.size = G.neighbors.size := by
  rw [neighbors_size_eq, neighbors_size_eq]
  have hp : (List.ofFn p.get).Perm (List.ofFn (fun i : Fin n => i)) := by
    apply (List.perm_ext_iff_of_nodup ?_ ?_).mpr
    · intro v
      simp only [List.mem_ofFn]
      exact ⟨fun _ => ⟨v, rfl⟩, fun _ => p.get_surj v⟩
    · change (List.ofFn p.get).Pairwise (· ≠ ·)
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      simp only [List.getElem_ofFn]
      intro he
      have := congrArg Fin.val (p.get_inj he)
      change i = j at this
      omega
    · change (List.ofFn (fun i : Fin n => i)).Pairwise (· ≠ ·)
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      simp only [List.getElem_ofFn]
      intro he
      have := congrArg Fin.val he
      change i = j at this
      omega
  have hs := (hp.map G.degree).sum_nat
  have hd : (G.relabel p).degree = fun i => G.degree (p.get i) := funext (degree_relabel G p)
  rw [hd]
  simpa only [List.map_ofFn, Function.comp_def] using hs

@[simp] theorem relabel_id (G : SparseGraph n) : G.relabel (Perm.id n) = G := by
  ext i j
  simp

theorem relabel_relabel (G : SparseGraph n) (p q : Perm n) :
    (G.relabel p).relabel q = G.relabel (p.comp q) := by
  ext i j
  simp

@[simp] theorem toDense_relabel (G : SparseGraph n) (p : Perm n) :
    (G.relabel p).toDense = G.toDense.relabel p.get := by
  ext i j
  simp

end Hex.SparseGraph
