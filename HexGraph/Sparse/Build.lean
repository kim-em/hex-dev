/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraph.Sparse
import all Init.Data.List.Basic

@[expose] public section

namespace Hex.SparseGraph

namespace Builder

/-- Remove consecutive duplicates in one pass. -/
def unique [BEq α] : List α → List α
  | [] => []
  | a :: xs => go a xs
where
  go (a : α) : List α → List α
    | [] => [a]
    | b :: xs => if a == b then go a xs else a :: go b xs

private theorem unique_loop [BEq α] (xs : List α) (a : α) (acc : List α) :
    List.eraseRepsBy.loop (· == ·) a xs acc = acc.reverse ++ unique.go a xs := by
  induction xs generalizing a acc with
  | nil => simp [List.eraseRepsBy.loop, unique.go]
  | cons b xs ih =>
    simp only [List.eraseRepsBy.loop, unique.go]
    split <;> simp_all [List.append_assoc]

/-- Use the standard tail-recursive implementation in compiled code. -/
@[csimp] theorem unique_eq_eraseReps : @unique = @List.eraseReps := by
  funext α inst xs
  cases xs with
  | nil => rfl
  | cons a xs => simpa [unique, List.eraseReps, List.eraseRepsBy] using (unique_loop xs a []).symm

theorem mem_go [BEq α] [LawfulBEq α] (a b : α) (xs : List α) :
    b ∈ unique.go a xs ↔ b = a ∨ b ∈ xs := by
  induction xs generalizing a with
  | nil => simp [unique.go]
  | cons c xs ih =>
    rw [unique.go]
    split <;> simp_all [List.mem_cons]

@[simp] theorem mem_unique [BEq α] [LawfulBEq α] (a : α) (xs : List α) :
    a ∈ unique xs ↔ a ∈ xs := by
  cases xs <;> simp [unique, mem_go]

private theorem sorted_go (a : Fin n) (xs : List (Fin n))
    (h : (a :: xs).Pairwise (· ≤ ·)) : (unique.go a xs).Pairwise (· < ·) := by
  induction xs generalizing a with
  | nil => simp [unique.go]
  | cons b xs ih =>
    rw [unique.go]
    split
    · rename_i he
      have : a = b := beq_iff_eq.mp he
      subst a
      exact ih b h.tail
    · rename_i he
      have hab : a.val < b.val := by
        have hl := (List.pairwise_cons.mp h).1 b (by simp)
        have hn : a ≠ b := by simpa using he
        have hv : a.val ≠ b.val := fun hh => hn (Fin.ext hh)
        omega
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih b h.tail⟩
      intro c hc
      rcases (mem_go b c xs).mp hc with rfl | hc
      · exact hab
      · exact Nat.lt_of_lt_of_le hab ((List.pairwise_cons.mp h.tail).1 c hc)

/-- Sort a row and collapse repeated neighbours in linear time after sorting. -/
def normalize (xs : List (Fin n)) : List (Fin n) :=
  unique (Hex.List.sort xs (fun a b => a ≤ b))

@[simp] theorem mem_normalize (a : Fin n) (xs : List (Fin n)) :
    a ∈ normalize xs ↔ a ∈ xs := by simp [normalize]

theorem sorted_normalize (xs : List (Fin n)) : (normalize xs).Pairwise (· < ·) := by
  have h : (Hex.List.sort xs (fun a b => a ≤ b)).Pairwise (· ≤ ·) := by
    simpa only [Hex.List.sort_eq, decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun a b : Fin n => a ≤ b)
        (by intro a b c; simp only [decide_eq_true_eq]; exact Nat.le_trans)
        (by intro a b; simp; omega) xs
  unfold normalize
  generalize Hex.List.sort xs (fun a b => a ≤ b) = ys at *
  cases ys with
  | nil => simp [unique]
  | cons a ys => exact sorted_go a ys h

/-- Scatter an undirected edge into its two rows; diagonal pairs are dropped. -/
def add (rows : Vector (List (Fin n)) n) (e : Fin n × Fin n) :
    Vector (List (Fin n)) n :=
  if e.1 == e.2 then rows
  else
    let rows := rows.set e.1.val (e.2 :: rows[e.1])
    rows.set e.2.val (e.1 :: rows[e.2])

theorem mem_add (rows : Vector (List (Fin n)) n) (e : Fin n × Fin n) (i j : Fin n) :
    j ∈ (add rows e)[i.val] ↔ j ∈ rows[i.val] ∨
      (i ≠ j ∧ (e = (i, j) ∨ e = (j, i))) := by
  rcases e with ⟨a, b⟩
  simp only [add, beq_iff_eq]
  split
  · rename_i h
    subst b
    simp only [Prod.mk.injEq]
    grind
  · rename_i h
    by_cases hbi : b = i <;> by_cases hai : a = i <;>
      simp_all [Fin.getElem_fin, Vector.getElem_set, Fin.val_inj, List.mem_cons, Prod.mk.injEq] <;>
      grind

/-- Build unsorted adjacency lists with one array update per directed edge. -/
def scatter (edges : List (Fin n × Fin n)) : Vector (List (Fin n)) n :=
  edges.foldl add (Vector.replicate n [])

private theorem mem_fold (edges : List (Fin n × Fin n))
    (rows : Vector (List (Fin n)) n) (i j : Fin n) :
    j ∈ (edges.foldl add rows)[i.val] ↔ j ∈ rows[i.val] ∨
      (i ≠ j ∧ ((i, j) ∈ edges ∨ (j, i) ∈ edges)) := by
  induction edges generalizing rows with
  | nil => simp
  | cons e edges ih =>
    rw [List.foldl_cons, ih, mem_add]
    simp only [List.mem_cons]
    grind

@[simp] theorem mem_scatter (edges : List (Fin n × Fin n)) (i j : Fin n) :
    j ∈ (scatter edges)[i.val] ↔ i ≠ j ∧ ((i, j) ∈ edges ∨ (j, i) ∈ edges) := by
  simp [scatter, mem_fold]

/-- Range-checking supplies erased proofs for the finite endpoints. -/
def checked (n : Nat) (edges : List (Nat × Nat)) (h : edges.all (Graph.validEdge n)) :
    List (Fin n × Fin n) :=
  edges.attach.map fun (e : {e : Nat × Nat // e ∈ edges}) =>
    have hv : e.val.1 < n ∧ e.val.2 < n ∧ e.val.1 ≠ e.val.2 := by
      simpa only [Graph.validEdge, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
        and_assoc] using List.all_eq_true.mp h e.val e.property
    (⟨e.val.1, hv.1⟩, ⟨e.val.2, hv.2.1⟩)

@[simp] theorem mem_checked (n : Nat) (edges : List (Nat × Nat)) (h) (i j : Fin n) :
    (i, j) ∈ checked n edges h ↔ (i.val, j.val) ∈ edges := by
  simp only [checked, List.mem_map]
  constructor
  · rintro ⟨e, _, he⟩
    have hh := congrArg (fun e : Fin n × Fin n => (e.1.val, e.2.val)) he
    simpa only [← hh, Prod.eta] using e.property
  · intro he
    exact ⟨⟨(i.val, j.val), he⟩, by simp, rfl⟩

end Builder

variable {n : Nat}

/-- Expose row normalization to the kernel while retaining the existing
array map in compiled graph construction. -/
def Builder.normalizeRows (rows : Vector (List (Fin n)) n) :
    Vector (List (Fin n)) n :=
  ⟨Hex.Array.map' Builder.normalize rows.toArray, by simp⟩

@[simp] theorem Builder.normalizeRows_eq (rows : Vector (List (Fin n)) n) :
    Builder.normalizeRows rows = rows.map Builder.normalize := by
  apply Vector.ext
  intro i hi
  simp [Builder.normalizeRows]

@[inline] def Builder.normalizeRowsFast (rows : Vector (List (Fin n)) n) :
    Vector (List (Fin n)) n := rows.map Builder.normalize

@[csimp] theorem Builder.normalizeRows_eq_map : @Builder.normalizeRows =
    @Builder.normalizeRowsFast := by
  funext n rows
  exact Builder.normalizeRows_eq rows

/-- Build from unordered `Fin` pairs, collapsing duplicates and dropping loops.
Scattering and packing are linear; each row is sorted separately. -/
def ofEdges (edges : List (Fin n × Fin n)) : SparseGraph n :=
  ofRows (Builder.normalizeRows (Builder.scatter edges))
    (fun i => by simpa using Builder.sorted_normalize ((Builder.scatter edges)[i]))
    (fun i j => by simp [Builder.mem_scatter, ne_comm, or_comm])
    (fun i => by simp)

@[simp] theorem adj_ofEdges (edges : List (Fin n × Fin n)) (i j : Fin n) :
    (ofEdges edges).adj i j =
      (i != j && (decide ((i, j) ∈ edges) || decide ((j, i) ∈ edges))) := by
  rw [Bool.eq_iff_iff, ← mem_nbrs, ← Array.mem_toList_iff, ofEdges, nbrs_ofRows]
  simp

@[simp] theorem toDense_ofEdges (edges : List (Fin n × Fin n)) :
    (ofEdges edges).toDense = Graph.ofEdges edges := by
  ext i j
  simp

/-- Checked edge-list builder: reject loops and out-of-range endpoints,
otherwise normalize duplicate undirected pairs into compressed rows. -/
def ofEdges? (n : Nat) (edges : List (Nat × Nat)) : Option (SparseGraph n) :=
  if h : edges.all (Graph.validEdge n) then some (ofEdges (Builder.checked n edges h))
  else none

theorem isSome_ofEdges? (n : Nat) (edges : List (Nat × Nat)) :
    (ofEdges? n edges).isSome = edges.all (Graph.validEdge n) := by
  rw [ofEdges?]
  split <;> simp_all

@[simp] theorem adj_ofEdges? {edges : List (Nat × Nat)} {G : SparseGraph n}
    (h : ofEdges? n edges = some G) (i j : Fin n) :
    G.adj i j = ((i.val, j.val) ∈ edges || (j.val, i.val) ∈ edges) := by
  rw [ofEdges?] at h
  split at h
  · rename_i hv
    injection h with he
    subst G
    rw [adj_ofEdges, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, decide_eq_true_eq,
      Builder.mem_checked]
    refine ⟨And.right, fun hh => ⟨?_, hh⟩⟩
    intro hij
    subst j
    have hmem : (i.val, i.val) ∈ edges := hh.elim id id
    have he := List.all_eq_true.mp hv _ hmem
    simp [Graph.validEdge] at he
  · simp at h

/-- The two checked constructors accept the same inputs and represent the same graph. -/
theorem toDense_ofEdges? (n : Nat) (edges : List (Nat × Nat)) :
    (ofEdges? n edges).map toDense = Graph.ofEdges? n edges := by
  cases hs : ofEdges? n edges with
  | none =>
    have hv := isSome_ofEdges? n edges
    rw [hs] at hv
    simp only [Option.isSome_none] at hv
    simp [Graph.ofEdges?, ← hv]
  | some G =>
    have hv := isSome_ofEdges? n edges
    rw [hs] at hv
    simp only [Option.isSome_some] at hv
    have hd := Graph.isSome_ofEdges? n edges
    rw [← hv] at hd
    obtain ⟨H, hH⟩ := Option.isSome_iff_exists.mp hd
    simp only [Option.map_some, hH, Option.some.injEq]
    ext i j
    rw [adj_toDense, adj_ofEdges? hs, Graph.adj_ofEdges? hH]

/-- Enumerate each undirected edge once, in increasing endpoint order. -/
def edges (G : SparseGraph n) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((G.nbrs i).toList.filter fun j => i < j).map fun j => (i, j)

@[simp] theorem mem_edges (G : SparseGraph n) (i j : Fin n) :
    (i, j) ∈ G.edges ↔ i < j ∧ G.adj i j = true := by
  simp only [edges, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
    List.mem_filter, Array.mem_toList_iff, mem_nbrs, decide_eq_true_eq, Prod.mk.injEq]
  grind

@[simp] theorem ofEdges_edges (G : SparseGraph n) : ofEdges G.edges = G := by
  ext i j
  rw [adj_ofEdges, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, decide_eq_true_eq, mem_edges,
    ← G.adj_symm i j]
  by_cases hij : i = j
  · subst j
    simp
  · constructor
    · grind
    · intro h
      refine ⟨hij, ?_⟩
      have hn : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
      by_cases ht : i < j
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨by omega, h⟩

end Hex.SparseGraph
