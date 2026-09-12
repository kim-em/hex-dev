/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Update
public import HexGraphIso.Nauty.Sparse.RowOrder

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A packed interval enumerates one normalized row, in arbitrary order. -/
structure RowRep (read : Nat → Nat) (lo hi : Nat) (row : List (Fin n)) : Prop where
  le : lo ≤ hi
  perm : ((List.range' lo (hi - lo)).map read).Perm (row.map Fin.val)

namespace RowRep

variable {read : Nat → Nat} {lo hi : Nat} {row : List (Fin n)}

theorem length (h : RowRep read lo hi row) : row.length = hi - lo := by
  simpa using h.perm.length_eq.symm

theorem mem_iff (h : RowRep read lo hi row) (v : Nat) :
    (∃ e, lo ≤ e ∧ e < hi ∧ read e = v) ↔ v ∈ row.map Fin.val := by
  rw [← h.perm.mem_iff, List.mem_map]
  simp only [List.mem_range'_1]
  constructor
  · rintro ⟨e, hlo, hhi, he⟩
    exact ⟨e, ⟨hlo, by omega⟩, he⟩
  · rintro ⟨e, ⟨hlo, hhi⟩, he⟩
    exact ⟨e, hlo, by omega, he⟩

theorem bound (h : RowRep read lo hi row) {e : Nat} (hlo : lo ≤ e) (hhi : e < hi) :
    read e < n := by
  obtain ⟨v, _, hv⟩ := List.mem_map.mp ((h.mem_iff _).mp ⟨e, hlo, hhi, rfl⟩)
  rw [← hv]
  exact v.isLt

theorem injective (h : RowRep read lo hi row) (hs : row.Pairwise (· < ·))
    {a b : Nat} (ha : lo ≤ a) (ha' : a < hi) (hb : lo ≤ b) (hb' : b < hi)
    (he : read a = read b) : a = b := by
  have hn : (row.map Fin.val).Nodup :=
    List.pairwise_map.mpr (hs.imp fun hlt => Nat.ne_of_lt hlt)
  have hp := h.perm.nodup_iff.mpr hn
  have hia : a - lo < ((List.range' lo (hi - lo)).map read).length := by simp; omega
  have hib : b - lo < ((List.range' lo (hi - lo)).map read).length := by simp; omega
  have hab := (hp.getElem_inj (hi := hia) (hj := hib)).mp (by
    simpa [List.getElem_map, List.getElem_range', Nat.add_sub_cancel' ha,
      Nat.add_sub_cancel' hb] using he)
  omega

private theorem array_scan (a : Array Nat) {lo hi : Nat} (hlo : lo ≤ hi)
    (hhi : hi ≤ a.size) :
    ((List.range' lo (hi - lo)).map fun e => a[e]!) = (a.extract lo hi).toList := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range', Array.length_toList, Array.size_extract]
    omega
  · intro i hi' hj
    have hb : lo + i < a.size := by simp only [List.length_map, List.length_range'] at hi'; omega
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul, Array.getElem_toList,
      Array.getElem_extract, getElem!_pos a (lo + i) hb]

/-- The canonical store's raw row has the represented row's members and degree. -/
theorem stored {R : Rows n} {H : Hex.SparseGraph n} (h : R.Prefix H n) (i : Fin n) :
    RowRep (fun e => R.neighbors[e]!) R.offsets[i.val]! R.offsets[i.val + 1]!
      (H.nbrs i).toList := by
  have hm : R.offsets[i.val]! ≤ R.offsets[i.val + 1]! := by
    rw [h.offsets_eq _ (by omega), h.offsets_eq _ (by omega)]
    exact H.offset_mono (by omega) (by omega)
  refine ⟨hm, ?_⟩
  rw [array_scan R.neighbors hm (h.offset_le (by omega))]
  exact h.rows_perm i i.isLt

/-- The candidate scan enumerates exactly its native relabelled row. -/
theorem candidate (G : Hex.SparseGraph n) {lab : Array Nat} {l : Label n}
    (hl : Label.ofArray? n lab = some l) (i : Fin n) :
    RowRep (fun e => (inverse n lab)[(Graph.ofGraph G).neighbor e]!)
      G.offsets[lab[i.val]!]! G.offsets[lab[i.val]! + 1]!
      ((G.relabel l.perm).nbrs i).toList := by
  refine ⟨?_, ?_⟩
  · rw [← Label.ofArray?_get hl i.val i.isLt]
    exact G.offset_mono (by omega) (by have := (l.get i).isLt; omega)
  · rw [source_row G lab l hl i]
    simpa only [Label.get, Label.toPerm, List.map_map, Function.comp_def] using
      ((G.nbrs_relabel_perm l.perm i).symm.map Fin.val)

end RowRep

end Hex.GraphIso.Nauty.Sparse
