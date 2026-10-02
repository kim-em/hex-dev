/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraph.Basic
public import HexBasic.Sort

public section

namespace Hex.SparseGraph

/-- Kernel-reducible offset accumulation, including the final endpoint. -/
@[expose] def offsetsFrom : List (List α) → Nat → List Nat
  | [], start => [start]
  | row :: rows, start => start :: offsetsFrom rows (start + row.length)

@[simp] theorem offsetsFrom_eq (rows : List (List α)) (start : Nat) :
    offsetsFrom rows start = rows.scanl (fun off row => off + row.length) start := by
  induction rows generalizing start with
  | nil => simp [offsetsFrom]
  | cons row rows ih => simp [offsetsFrom, ih, List.scanl_cons]

/-- Offsets of consecutive adjacency rows, including the final endpoint. -/
@[expose] def offsetsOf (rows : List (List α)) : List Nat := offsetsFrom rows 0

private theorem fold_lengths (rows : List (List α)) (start : Nat) :
    rows.foldl (fun off row => off + row.length) start = start + rows.flatten.length := by
  induction rows generalizing start with
  | nil => simp
  | cons row rows ih => simp [ih, Nat.add_assoc]

@[simp] theorem length_offsetsOf (rows : List (List α)) :
    (offsetsOf rows).length = rows.length + 1 := by simp [offsetsOf]

/-- An offset is the size of the preceding rows. -/
theorem get_offsetsOf (rows : List (List α)) (i : Nat) (hi : i ≤ rows.length) :
    (offsetsOf rows)[i]'(by simp; omega) = (rows.take i).flatten.length := by
  simp [offsetsOf, fold_lengths]

private theorem take_lengths (rows : List (List α)) (i : Nat) (hi : i < rows.length) :
    (rows.take (i + 1)).flatten.length = (rows.take i).flatten.length + rows[i].length := by
  rw [List.take_add_one]
  simp only [List.getElem?_eq_getElem hi, Option.toList_some, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]

private theorem slice_flatten (rows : List (List α)) (i : Nat) (hi : i < rows.length) :
    (rows.flatten.drop (rows.take i).flatten.length).take rows[i].length = rows[i] := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
    cases i with
    | zero => simp
    | succ i =>
      simpa only [List.take_succ_cons, List.flatten_cons, List.length_append,
        List.getElem_cons_succ, List.drop_length_add_append] using ih i (by simpa using hi)

/-- A row of compressed adjacency, with an exclusive end offset. -/
@[expose] def row (offsets : Array Nat) (neighbors : Array α) (i : Nat) : Array α :=
  neighbors.extract offsets[i]! offsets[i + 1]!

/-- Packing consecutive rows and extracting one recovers it exactly. -/
theorem row_pack (rows : List (List α)) (i : Nat) (hi : i < rows.length) :
    (row (offsetsOf rows).toArray rows.flatten.toArray i).toList = rows[i] := by
  rw [row, Array.toList_extract]
  have h₀ : (offsetsOf rows).toArray[i]! = (rows.take i).flatten.length := by
    rw [getElem!_pos _ _ (by simp; omega), List.getElem_toArray]
    exact get_offsetsOf rows i (by omega)
  have h₁ : (offsetsOf rows).toArray[i + 1]! = (rows.take (i + 1)).flatten.length := by
    rw [getElem!_pos _ _ (by simp; omega), List.getElem_toArray]
    exact get_offsetsOf rows (i + 1) (by omega)
  rw [h₀, h₁, take_lengths rows i hi]
  simpa using slice_flatten rows i hi

/-- The arrays consist of exactly `n` consecutive rows, without gaps or padding.
The row witness is proof data and is erased from the executable graph. -/
@[expose] def Layout (n : Nat) (offsets : Array Nat) (neighbors : Array α) : Prop :=
  ∃ rows : List (List α), rows.length = n ∧
    offsets = (offsetsOf rows).toArray ∧ neighbors = rows.flatten.toArray

end Hex.SparseGraph

namespace Hex

/-- A finite simple undirected graph with compressed, sorted adjacency lists. -/
structure SparseGraph (n : Nat) where
  /-- Start of each row and the final endpoint. -/
  offsets : Array Nat
  /-- Consecutive neighbour lists. -/
  neighbors : Array (Fin n)
  /-- Every adjacency entry belongs to exactly one row. -/
  layout : SparseGraph.Layout n offsets neighbors
  /-- Rows are strictly increasing, hence duplicate-free. -/
  sorted : ∀ i : Fin n, (SparseGraph.row offsets neighbors i.val).toList.Pairwise (· < ·)
  /-- Every edge has its reverse. -/
  symm : ∀ i j : Fin n, j ∈ SparseGraph.row offsets neighbors i.val ↔
    i ∈ SparseGraph.row offsets neighbors j.val
  /-- No vertex is adjacent to itself. -/
  loopless : ∀ i : Fin n, i ∉ SparseGraph.row offsets neighbors i.val

namespace SparseGraph

variable {n : Nat}

/-- The sorted neighbours of a vertex. Extracting a row copies its entries. -/
@[expose] def nbrs (G : SparseGraph n) (i : Fin n) : Array (Fin n) :=
  row G.offsets G.neighbors i.val

/-- Adjacency is membership in a compressed row. -/
@[expose] def adj (G : SparseGraph n) (i j : Fin n) : Bool :=
  (G.nbrs i).contains j

@[simp] theorem mem_nbrs (G : SparseGraph n) (i j : Fin n) :
    j ∈ G.nbrs i ↔ G.adj i j = true := by simp [adj]

theorem adj_symm (G : SparseGraph n) (i j : Fin n) : G.adj i j = G.adj j i := by
  rw [Bool.eq_iff_iff, ← mem_nbrs, ← mem_nbrs]
  exact G.symm i j

@[simp] theorem adj_self (G : SparseGraph n) (i : Fin n) : G.adj i i = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact G.loopless i ((mem_nbrs G i i).mpr h)

/-- Degree is the difference between consecutive offsets. -/
@[expose] def degree (G : SparseGraph n) (i : Fin n) : Nat :=
  G.offsets[i.val + 1]! - G.offsets[i.val]!

/-- Pack a vector of sorted, symmetric, loopless neighbour lists. -/
@[expose] def ofRows (rows : Vector (List (Fin n)) n)
    (hs : ∀ i : Fin n, (rows[i]).Pairwise (· < ·))
    (hr : ∀ i j : Fin n, j ∈ rows[i] ↔ i ∈ rows[j])
    (hl : ∀ i : Fin n, i ∉ rows[i]) : SparseGraph n where
  offsets := (offsetsOf rows.toList).toArray
  neighbors := rows.toList.flatten.toArray
  layout := by exact ⟨rows.toList, by simp, rfl, rfl⟩
  sorted i := by
    simpa only [row_pack rows.toList i.val (by simp),
      Vector.getElem_toList, Fin.getElem_fin] using hs i
  symm i j := by
    simpa only [← Array.mem_toList_iff, row_pack rows.toList i.val (by simp),
      row_pack rows.toList j.val (by simp), Vector.getElem_toList,
      Fin.getElem_fin] using hr i j
  loopless i := by
    simpa only [← Array.mem_toList_iff, row_pack rows.toList i.val (by simp),
      Vector.getElem_toList, Fin.getElem_fin] using hl i

@[simp] theorem nbrs_ofRows (rows : Vector (List (Fin n)) n) (hs hr hl) (i : Fin n) :
    ((ofRows rows hs hr hl).nbrs i).toList = rows[i] := by
  change (row (offsetsOf rows.toList).toArray rows.toList.flatten.toArray i.val).toList = _
  rw [row_pack rows.toList i.val (by simp)]
  exact Vector.getElem_toList _

/-- Dense conversion is explicit and allocates the full Boolean matrix. -/
@[expose] def toDense (G : SparseGraph n) : Graph n :=
  Graph.ofAdj G.adj G.adj_symm G.adj_self

@[simp] theorem adj_toDense (G : SparseGraph n) (i j : Fin n) :
    G.toDense.adj i j = G.adj i j := Graph.adj_ofAdj ..

/-- The offset array includes both endpoints of every row. -/
@[simp] theorem size_offsets (G : SparseGraph n) : G.offsets.size = n + 1 := by
  obtain ⟨rows, hlen, ho, _⟩ := G.layout
  simp [ho, hlen]

@[simp] theorem offset_zero (G : SparseGraph n) : G.offsets[0]! = 0 := by
  obtain ⟨rows, _, ho, _⟩ := G.layout
  simp [ho, offsetsOf]

@[simp] theorem offset_last (G : SparseGraph n) : G.offsets[n]! = G.neighbors.size := by
  obtain ⟨rows, hlen, ho, hn⟩ := G.layout
  rw [ho, hn, getElem!_pos _ _ (by simp; omega), List.getElem_toArray,
    get_offsetsOf rows n (by omega)]
  rw [List.take_of_length_le (by omega)]
  simp

/-- The constant-time degree operation counts the entries of the row. -/
theorem degree_eq_size (G : SparseGraph n) (i : Fin n) : G.degree i = (G.nbrs i).size := by
  obtain ⟨rows, hlen, ho, hn⟩ := G.layout
  have hi : i.val < rows.length := by omega
  rw [degree, ho, getElem!_pos _ _ (by simp; omega),
    getElem!_pos _ _ (by simp; omega), List.getElem_toArray, List.getElem_toArray,
    get_offsetsOf rows (i.val + 1) (by omega), get_offsetsOf rows i.val (by omega),
    take_lengths rows i.val hi, Nat.add_sub_cancel_left]
  rw [← Array.length_toList, nbrs, ho, hn, row_pack rows i.val hi]

/-- Equality of the two stored arrays determines the graph. -/
theorem ext_arrays {G H : SparseGraph n}
    (ho : G.offsets = H.offsets) (hn : G.neighbors = H.neighbors) : G = H := by
  cases G; cases H; cases ho; cases hn; rfl

/-- Sorted rows and a packed layout make graph equality extensional. -/
@[ext] theorem ext {G H : SparseGraph n} (h : ∀ i j, G.adj i j = H.adj i j) : G = H := by
  have hnbr : ∀ i, (G.nbrs i).toList = (H.nbrs i).toList := by
    intro i
    apply List.Perm.eq_of_pairwise (le := (· < ·))
      (fun a b _ _ hab hba => False.elim (by exact Nat.lt_irrefl a.val (Nat.lt_trans hab hba)))
      (G.sorted i) (H.sorted i)
    apply (List.perm_ext_iff_of_nodup
      ((G.sorted i).imp fun hab => Fin.ne_of_lt hab)
      ((H.sorted i).imp fun hab => Fin.ne_of_lt hab)).mpr
    intro j
    change j ∈ (G.nbrs i).toList ↔ j ∈ (H.nbrs i).toList
    rw [Array.mem_toList_iff, Array.mem_toList_iff, mem_nbrs, mem_nbrs, h]
  obtain ⟨rs, hr, hro, hrn⟩ := G.layout
  obtain ⟨ss, hs, hso, hsn⟩ := H.layout
  have he : rs = ss := by
    apply List.ext_getElem (hr.trans hs.symm)
    intro i hi hj
    have hh := hnbr ⟨i, by omega⟩
    simpa only [nbrs, hro, hrn, hso, hsn, row_pack rs i hi, row_pack ss i hj] using hh
  exact ext_arrays (by rw [hro, hso, he]) (by rw [hrn, hsn, he])

theorem eq_iff_adj {G H : SparseGraph n} : G = H ↔ ∀ i j, G.adj i j = H.adj i j :=
  ⟨fun h _ _ => h ▸ rfl, ext⟩

instance : DecidableEq (SparseGraph n) := fun G H =>
  if ho : G.offsets = H.offsets then
    if hn : G.neighbors = H.neighbors then .isTrue (ext_arrays ho hn)
    else .isFalse (fun h => hn (congrArg SparseGraph.neighbors h))
  else .isFalse (fun h => ho (congrArg SparseGraph.offsets h))

/-- The edgeless graph stores `n + 1` zero offsets and no neighbours. -/
@[expose] def empty (n : Nat) : SparseGraph n :=
  ofRows (Vector.replicate n []) (by simp) (by simp) (by simp)

@[simp] theorem adj_empty (i j : Fin n) : (empty n).adj i j = false := by
  apply Bool.eq_false_iff.mpr
  simp [← mem_nbrs, empty, ← Array.mem_toList_iff]

end SparseGraph

namespace Graph

/-- Explicit conversion scans the dense matrix once to build sorted sparse rows. -/
@[expose] def toSparse (G : Graph n) : SparseGraph n :=
  SparseGraph.ofRows (Vector.ofFn fun i => (G.nbrs i).toList)
    (fun i => by simpa [nbrs] using (List.pairwise_lt_finRange n).filter (p := G.adj i))
    (fun i j => by simp only [Fin.getElem_fin, Vector.getElem_ofFn,
      Array.mem_toList_iff, mem_nbrs]; exact Bool.eq_iff_iff.mp (G.adj_symm i j))
    (fun i => by simp [mem_nbrs])

@[simp] theorem adj_toSparse (G : Graph n) (i j : Fin n) :
    G.toSparse.adj i j = G.adj i j := by
  rw [Bool.eq_iff_iff, ← SparseGraph.mem_nbrs, ← Array.mem_toList_iff,
    toSparse, SparseGraph.nbrs_ofRows]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Array.mem_toList_iff, mem_nbrs]

@[simp] theorem toDense_toSparse (G : Graph n) : G.toSparse.toDense = G := by
  ext i j
  simp

end Graph

namespace SparseGraph

@[simp] theorem toSparse_toDense (G : SparseGraph n) : G.toDense.toSparse = G := by
  ext i j
  simp

end SparseGraph
end Hex
