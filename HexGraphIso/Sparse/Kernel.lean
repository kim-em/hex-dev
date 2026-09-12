/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Sparse.Iso
public import HexGraphIso.Kernel.IsoLit

public section

namespace Hex.GraphIso.Sparse.Kernel

variable {n k : Nat}

/-- Sorted neighbour literals, with one list per vertex. -/
@[expose] def rows (G : SparseGraph n) : List (List Nat) :=
  List.ofFn fun i => (G.nbrs i).toList.map Fin.val

theorem atD_rows (G : SparseGraph n) (i : Fin n) :
    atD (rows G) i.val [] = (G.nbrs i).toList.map Fin.val := by
  rw [atD_eq_getElem _ _ (by simp [rows])]
  simp [rows]

theorem atD_perm (p : Perm n) (i : Fin n) :
    atD (p.vec.toList.map Fin.val) i.val 0 = (p.get i).val := by
  rw [atD_eq_getElem _ _ (by simp), List.getElem_map, Perm.get_toList]

theorem atD_color (c : Coloring n k) (i : Fin n) :
    atD (c.cells.toList.map Fin.val) i.val 0 = c.cells[i].val := by
  rw [atD_eq_getElem _ _ (by simp), List.getElem_map]
  simp

/-- Validate a forward transporter on sparse literals. Sorting each mapped
neighbour list checks exact row equality without scanning non-edges.
The accompanying soundness theorem requires a checked permutation and
equalities identifying all literals with their original graph data. -/
@[expose] def checkIso (n : Nat) (rowsA rowsB : List (List Nat))
    (cellsA cellsB images : List Nat) : Bool :=
  (List.range n).all fun i =>
    atD cellsB (atD images i 0) 0 == atD cellsA i 0 &&
    Hex.List.sort ((atD rowsA i []).map (fun j => atD images j 0)) (fun a b => a ≤ b) ==
      atD rowsB (atD images i 0) []

private theorem image_row (G : SparseGraph n) (p : Perm n) (i : Fin n) :
    ((G.nbrs i).toList.map Fin.val).map
      (fun j => atD (p.vec.toList.map Fin.val) j 0) =
      (G.nbrs i).toList.map (fun j => (p.get j).val) := by
  simp only [List.map_map]
  congr 1
  funext j
  exact atD_perm p j

private theorem mem_image (G : SparseGraph n) (p : Perm n) (i j : Fin n) :
    (p.get j).val ∈ (G.nbrs i).toList.map (fun v => (p.get v).val) ↔
      G.adj i j = true := by
  rw [List.mem_map, ← SparseGraph.mem_nbrs, ← Array.mem_toList_iff]
  constructor
  · rintro ⟨v, hv, he⟩
    exact p.get_inj (Fin.ext he) ▸ hv
  · intro hj
    exact ⟨j, hj, rfl⟩

private theorem mem_row (G : SparseGraph n) (i j : Fin n) :
    j.val ∈ (G.nbrs i).toList.map Fin.val ↔ G.adj i j = true := by
  simpa using mem_image G (Perm.id n) i j

private theorem sorted_image {G H : Colored n k} {p : Perm n}
    (h : IsIso G H p) (i : Fin n) :
    Hex.List.sort ((G.graph.nbrs i).toList.map (fun v => (p.get v).val)) (fun a b => a ≤ b) =
      (H.graph.nbrs (p.get i)).toList.map Fin.val := by
  rw [Hex.List.sort_eq]
  have hp : ((G.graph.nbrs i).toList.map p.get).Perm
      (H.graph.nbrs (p.get i)).toList := by
    apply (List.perm_ext_iff_of_nodup
      ((G.graph.sorted i).map p.get (fun a b hab he => Fin.ne_of_lt hab (p.get_inj he)))
      ((H.graph.sorted (p.get i)).imp fun hab => Fin.ne_of_lt hab)).mpr
    intro w
    rw [List.mem_map, Array.mem_toList_iff]
    change (∃ v, v ∈ (G.graph.nbrs i).toList ∧ p.get v = w) ↔
      w ∈ H.graph.nbrs (p.get i)
    rw [SparseGraph.mem_nbrs]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [h.adj_eq]
      exact (SparseGraph.mem_nbrs ..).mp (Array.mem_toList_iff.mp hv)
    · intro hw
      refine ⟨p.inv.get w, ?_, p.get_inv_get w⟩
      rw [Array.mem_toList_iff, SparseGraph.mem_nbrs]
      rw [← h.adj_eq, Perm.get_inv_get]
      exact hw
  have hm := hp.map Fin.val
  simp only [List.map_map] at hm
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
    (fun _ _ _ _ hab hba => Nat.le_antisymm hab hba) ?_ ?_
    ((List.mergeSort_perm _ _).trans hm)
  · simpa only [decide_eq_true_eq] using List.pairwise_mergeSort
      (le := fun a b : Nat => a ≤ b)
      (by intro a b c; simp only [decide_eq_true_eq]; exact Nat.le_trans)
      (by intro a b; simp; omega) _
  · exact (H.graph.sorted (p.get i)).map Fin.val (fun _ _ h => Nat.le_of_lt h)

/-- Every genuine transporter passes the sparse literal checker. -/
theorem checkIso_of_isIso {G H : Colored n k} {p : Perm n} (h : IsIso G H p) :
    checkIso n (rows G.graph) (rows H.graph)
      (G.coloring.cells.toList.map Fin.val) (H.coloring.cells.toList.map Fin.val)
      (p.vec.toList.map Fin.val) = true := by
  simp only [checkIso, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  intro i hi
  have hv : i = (⟨i, hi⟩ : Fin n).val := rfl
  rw [hv, atD_perm, atD_color, atD_color, atD_rows, atD_rows, image_row]
  exact ⟨congrArg Fin.val (h.cells_eq ⟨i, hi⟩), sorted_image h ⟨i, hi⟩⟩

/-- A kernel check on identified sparse literals proves the transporter. -/
theorem isIso_of_checkIso {G H : Colored n k} {p : Perm n}
    {RA RB : List (List Nat)} {CA CB PL : List Nat}
    (hA : rows G.graph = RA) (hB : rows H.graph = RB)
    (hcA : G.coloring.cells.toList.map Fin.val = CA)
    (hcB : H.coloring.cells.toList.map Fin.val = CB)
    (hp : p.vec.toList.map Fin.val = PL)
    (hchk : checkIso n RA RB CA CB PL = true) : IsIso G H p := by
  subst hA hB hcA hcB hp
  simp only [checkIso, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq] at hchk
  apply IsIso.mk
  · intro i
    have hc := (hchk i.val i.isLt).1
    rw [atD_perm, atD_color, atD_color] at hc
    exact Fin.ext hc
  · intro i j
    have hr := (hchk i.val i.isLt).2
    rw [atD_perm, atD_rows, atD_rows, image_row] at hr
    have hm := congrArg (fun r : List Nat => (p.get j).val ∈ r) hr
    simp only [Hex.List.sort_eq, List.mem_mergeSort, mem_image, mem_row] at hm
    exact Bool.eq_iff_iff.mpr (Iff.of_eq hm.symm)

theorem isomorphic_of_checkIso {G H : Colored n k} {p : Perm n}
    {RA RB : List (List Nat)} {CA CB PL : List Nat}
    (hA : rows G.graph = RA) (hB : rows H.graph = RB)
    (hcA : G.coloring.cells.toList.map Fin.val = CA)
    (hcB : H.coloring.cells.toList.map Fin.val = CB)
    (hp : p.vec.toList.map Fin.val = PL)
    (hchk : checkIso n RA RB CA CB PL = true) : Isomorphic G H :=
  Isomorphic.intro p (isIso_of_checkIso hA hB hcA hcB hp hchk)

/-- Literal and native checking agree on the same checked permutation. -/
theorem checkIso_eq (G H : Colored n k) (p : Perm n) :
    checkIso n (rows G.graph) (rows H.graph)
      (G.coloring.cells.toList.map Fin.val) (H.coloring.cells.toList.map Fin.val)
      (p.vec.toList.map Fin.val) = Sparse.checkIso G H p := by
  rw [Bool.eq_iff_iff, Sparse.checkIso_iff]
  exact ⟨fun h => isIso_of_checkIso rfl rfl rfl rfl rfl h, checkIso_of_isIso⟩

end Hex.GraphIso.Sparse.Kernel
