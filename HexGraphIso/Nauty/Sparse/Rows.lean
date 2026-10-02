/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Graph

public section

namespace Hex.SparseGraph

variable {n : Nat}

/-- Consecutive packed rows have monotone offsets, including the terminal offset. -/
theorem offset_mono (G : SparseGraph n) {i j : Nat} (hij : i ≤ j) (hj : j ≤ n) :
    G.offsets[i]! ≤ G.offsets[j]! := by
  obtain ⟨rows, hlen, ho, _⟩ := G.layout
  rw [ho, getElem!_pos _ i (by simp; omega),
    getElem!_pos _ j (by simp; omega), List.getElem_toArray, List.getElem_toArray,
    get_offsetsOf rows i (by omega), get_offsetsOf rows j (by omega)]
  obtain ⟨tail, ht⟩ := List.take_prefix_take_left (l := rows) hij
  rw [← ht, List.flatten_append, List.length_append]
  omega

theorem offset_le (G : SparseGraph n) {i : Nat} (hi : i ≤ n) :
    G.offsets[i]! ≤ G.neighbors.size := by
  have h := G.offset_mono hi (Nat.le_refl n)
  rw [G.offset_last] at h
  exact h

/-- An adjacency-loop cursor is inside the packed neighbour array. -/
theorem edge_lt (G : SparseGraph n) {i : Fin n} {e : Nat}
    (he : e < G.offsets[i.val + 1]!) : e < G.neighbors.size :=
  Nat.lt_of_lt_of_le he (G.offset_le (by omega))

/-- Reading a packed entry in a row supplies an actual neighbour. -/
theorem edge_mem (G : SparseGraph n) (i : Fin n) {e : Nat}
    (hlo : G.offsets[i.val]! ≤ e) (hhi : e < G.offsets[i.val + 1]!) :
    G.neighbors[e]'(G.edge_lt hhi) ∈ G.nbrs i := by
  apply Array.mem_extract_iff_getElem.mpr
  refine ⟨e - G.offsets[i.val]!, ?_, ?_⟩
  · rw [Nat.min_eq_left (G.offset_le (by omega))]
    omega
  · congr 1
    omega

/-- Every row member is reached by a cursor of the adjacency loop. -/
theorem mem_edge (G : SparseGraph n) {i v : Fin n} (hv : v ∈ G.nbrs i) :
    ∃ e, G.offsets[i.val]! ≤ e ∧ e < G.offsets[i.val + 1]! ∧
      G.neighbors[e]? = some v := by
  obtain ⟨k, hk, he⟩ := Array.mem_extract_iff_getElem.mp hv
  refine ⟨G.offsets[i.val]! + k, by omega, by omega, ?_⟩
  rw [getElem?_pos _ _ (by omega), he]

end Hex.SparseGraph

namespace Hex.GraphIso.Nauty.Sparse

/-- Valid input views are precisely native simple sparse graphs. -/
def Graph.Valid (g : Graph n) : Prop := ∃ G : Hex.SparseGraph n, g = .ofGraph G

theorem Graph.valid_ofGraph (G : Hex.SparseGraph n) : (Graph.ofGraph G).Valid :=
  ⟨G, rfl⟩

theorem Graph.neighbor_lt (G : Hex.SparseGraph n) (i : Fin n) {e : Nat}
    (he : e < G.offsets[i.val + 1]!) : (Graph.ofGraph G).neighbor e < n := by
  rw [Graph.neighbor_ofGraph G e (G.edge_lt he)]
  exact (G.neighbors[e]'(G.edge_lt he)).isLt

/-- A partially installed canonical graph. Only its first `count` rows and
their offsets describe `G`; the remaining entries are allocated scratch.
Rows retain their unsorted nauty order, so row correctness is a permutation. -/
structure Rows.Prefix (R : Rows n) (G : Hex.SparseGraph n) (count : Nat) : Prop where
  count_le : count ≤ n
  offsets_size : R.offsets.size = n + 1
  neighbors_size : R.neighbors.size = G.neighbors.size
  offsets_eq : ∀ i, i ≤ count → R.offsets[i]! = G.offsets[i]!
  rows_perm : ∀ i : Fin n, i.val < count →
    (Hex.SparseGraph.row R.offsets R.neighbors i.val).toList.Perm
      ((G.nbrs i).toList.map Fin.val)

namespace Rows.Prefix

theorem mono {R : Rows n} {G : Hex.SparseGraph n} {count small : Nat}
    (h : R.Prefix G count) (hs : small ≤ count) : R.Prefix G small :=
  ⟨Nat.le_trans hs h.count_le, h.offsets_size, h.neighbors_size,
    fun i hi => h.offsets_eq i (Nat.le_trans hi hs),
    fun i hi => h.rows_perm i (Nat.lt_of_lt_of_le hi hs)⟩

theorem offset_le {R : Rows n} {G : Hex.SparseGraph n} {count i : Nat}
    (h : R.Prefix G count) (hi : i ≤ count) : R.offsets[i]! ≤ R.neighbors.size := by
  rw [h.offsets_eq i hi, h.neighbors_size]
  exact G.offset_le (Nat.le_trans hi h.count_le)

theorem degree_eq {R : Rows n} {G : Hex.SparseGraph n} {count : Nat}
    (h : R.Prefix G count) (i : Fin n) (hi : i.val < count) :
    R.degree i.val = G.degree i := by
  simp only [Rows.degree, Hex.SparseGraph.degree,
    h.offsets_eq i.val (by omega), h.offsets_eq (i.val + 1) (by omega)]

/-- Membership in an installed row agrees with the canonical graph. -/
theorem mem_iff {R : Rows n} {G : Hex.SparseGraph n} {count : Nat}
    (h : R.Prefix G count) (i v : Fin n) (hi : i.val < count) :
    v.val ∈ Hex.SparseGraph.row R.offsets R.neighbors i.val ↔ G.adj i v = true := by
  rw [← Array.mem_toList_iff, (h.rows_perm i hi).mem_iff,
    List.mem_map, ← Hex.SparseGraph.mem_nbrs]
  constructor
  · rintro ⟨w, hw, he⟩
    have : w = v := Fin.ext he
    subst w
    exact Array.mem_toList_iff.mp hw
  · intro hv
    exact ⟨v, Array.mem_toList_iff.mpr hv, rfl⟩

/-- An entry of an installed row is a vertex, even though the store is raw. -/
theorem entry_lt {R : Rows n} {G : Hex.SparseGraph n} {count e : Nat}
    (h : R.Prefix G count) (i : Fin n) (hi : i.val < count)
    (hlo : R.offsets[i.val]! ≤ e) (hhi : e < R.offsets[i.val + 1]!) :
    R.neighbors[e]! < n := by
  have hbound := h.offset_le (i := i.val + 1) (by omega)
  have he : e < R.neighbors.size := by omega
  have hm : R.neighbors[e]! ∈ Hex.SparseGraph.row R.offsets R.neighbors i.val := by
    apply Array.mem_extract_iff_getElem.mpr
    refine ⟨e - R.offsets[i.val]!, ?_, ?_⟩
    · rw [Nat.min_eq_left hbound]
      omega
    · rw [getElem!_pos _ e he]
      congr 1
      omega
  have hn := (h.rows_perm i hi).mem_iff.mp (Array.mem_toList_iff.mpr hm)
  obtain ⟨v, _, hv⟩ := List.mem_map.mp hn
  rw [← hv]
  exact v.isLt

theorem blank (G : Hex.SparseGraph n) : (Graph.ofGraph G).blank.Prefix G 0 := by
  refine ⟨by omega, by simp [Graph.blank], by simp [Graph.blank, Graph.ofGraph], ?_, ?_⟩
  · intro i hi
    have : i = 0 := by omega
    subst i
    rw [G.offset_zero]
    simp [Graph.blank]
  · intro i hi
    omega

end Rows.Prefix

end Hex.GraphIso.Nauty.Sparse
