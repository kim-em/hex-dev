/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic

public section

/-!
Finite simple undirected graphs on the vertex set `Fin n`.

The representation is a dense Boolean adjacency matrix together with
symmetry and looplessness invariants, so every value of `Graph n` is a
simple undirected graph and equality of values is exactly equality of the
represented edge relation (`Graph.ext` / `Graph.eq_iff_adj`). Adjacency is
an `O(1)` executable read; `DecidableEq` compares the underlying matrix and
is kernel-reducible, which keeps fixture comparison in downstream
conformance suites cheap.

The checked edge-list builder `ofEdges?` rejects out-of-range endpoints and
loops and collapses duplicate undirected edges. `nbrs` materializes the
sorted duplicate-free neighbour array of a vertex. `relabel` composes the
adjacency relation with a vertex map and satisfies the adjacency
correspondence `adj_relabel` definitionally on entries.
-/

namespace Hex

/-- A finite simple undirected graph on the vertex set `Fin n`, as a dense
Boolean adjacency matrix constrained to be symmetric and loopless. -/
structure Graph (n : Nat) where
  /-- The dense Boolean adjacency matrix. -/
  adjMatrix : Matrix Bool n n
  /-- The edge relation is symmetric. -/
  symm : ∀ i j : Fin n, adjMatrix[i][j] = adjMatrix[j][i]
  /-- The edge relation is irreflexive: no loops. -/
  loopless : ∀ i : Fin n, adjMatrix[i][i] = false

namespace Graph

variable {n : Nat}

/-- Executable adjacency test: `G.adj i j` is `true` exactly when `{i, j}` is
an edge of `G`. `O(1)`. -/
@[inline, expose] def adj (G : Graph n) (i j : Fin n) : Bool :=
  G.adjMatrix[(i, j)]

/-- `adj` reads the adjacency matrix entry. -/
theorem adj_eq_getElem (G : Graph n) (i j : Fin n) :
    G.adj i j = G.adjMatrix[i][j] := by
  rw [adj, Matrix.getElem_pair_eq_nested]

/-- Adjacency is symmetric. -/
theorem adj_symm (G : Graph n) (i j : Fin n) : G.adj i j = G.adj j i := by
  rw [adj_eq_getElem, adj_eq_getElem]
  exact G.symm i j

/-- Adjacency is irreflexive. -/
@[simp] theorem adj_self (G : Graph n) (i : Fin n) : G.adj i i = false := by
  rw [adj_eq_getElem]
  exact G.loopless i

/-- Adjacent vertices are distinct. -/
theorem ne_of_adj {G : Graph n} {i j : Fin n} (h : G.adj i j = true) : i ≠ j := by
  intro rfl
  rw [adj_self] at h
  exact Bool.false_ne_true h

/-- Two graphs with equal adjacency matrices are equal. -/
theorem ext_adjMatrix {G H : Graph n} (h : G.adjMatrix = H.adjMatrix) : G = H := by
  cases G; cases H; cases h; rfl

/-- Two graphs are equal when they have the same edges. -/
@[ext] theorem ext {G H : Graph n} (h : ∀ i j, G.adj i j = H.adj i j) : G = H := by
  refine ext_adjMatrix (Matrix.ext_getElem fun i j => ?_)
  rw [← adj_eq_getElem, ← adj_eq_getElem]
  exact h i j

/-- Equality of graphs is exactly equality of the represented edge relation. -/
theorem eq_iff_adj {G H : Graph n} : G = H ↔ ∀ i j, G.adj i j = H.adj i j :=
  ⟨fun h _ _ => h ▸ rfl, ext⟩

@[expose] instance : DecidableEq (Graph n) := fun G H =>
  if h : G.adjMatrix.data = H.adjMatrix.data then
    .isTrue (ext_adjMatrix (Matrix.ext_data h))
  else
    .isFalse fun e => h (congrArg (fun K : Graph n => K.adjMatrix.data) e)

/-! # Construction -/

/-- Build a graph from a symmetric irreflexive Boolean adjacency function. -/
@[expose] def ofAdj (f : Fin n → Fin n → Bool)
    (hs : ∀ i j, f i j = f j i) (hi : ∀ i, f i i = false) : Graph n where
  adjMatrix := Matrix.ofFn f
  symm i j := by rw [Matrix.getElem_ofFn, Matrix.getElem_ofFn]; exact hs i j
  loopless i := by rw [Matrix.getElem_ofFn]; exact hi i

@[simp] theorem adj_ofAdj (f : Fin n → Fin n → Bool)
    (hs : ∀ i j, f i j = f j i) (hi : ∀ i, f i i = false) (i j : Fin n) :
    (ofAdj f hs hi).adj i j = f i j := by
  rw [adj_eq_getElem, ofAdj, Matrix.getElem_ofFn]

/-- The graph on `n` vertices with no edges. -/
@[expose] def empty (n : Nat) : Graph n :=
  ofAdj (fun _ _ => false) (fun _ _ => rfl) (fun _ => rfl)

@[simp] theorem adj_empty (i j : Fin n) : (empty n).adj i j = false :=
  adj_ofAdj ..

/-- The complete graph on `n` vertices. -/
@[expose] def complete (n : Nat) : Graph n :=
  ofAdj (fun i j => i != j)
    (fun i j => by simp [bne_comm])
    (fun i => by simp)

@[simp] theorem adj_complete (i j : Fin n) : (complete n).adj i j = (i != j) :=
  adj_ofAdj ..

/-! # Checked edge-list builder -/

/-- The membership test behind `ofEdges?`: an unordered edge `{i, j}` is
present when the input list contains it in either orientation. -/
@[expose] def edgeListAdj (edges : List (Nat × Nat)) (i j : Fin n) : Bool :=
  edges.any fun e => (e.1 == i.val && e.2 == j.val) || (e.1 == j.val && e.2 == i.val)

theorem edgeListAdj_symm (edges : List (Nat × Nat)) (i j : Fin n) :
    edgeListAdj edges i j = edgeListAdj edges j i := by
  rw [Bool.eq_iff_iff, edgeListAdj, edgeListAdj, List.any_eq_true, List.any_eq_true]
  constructor <;>
    · rintro ⟨e, he, hor⟩
      exact ⟨e, he, by revert hor; simp +contextual [Bool.or_comm]⟩

/-- A well-formed input for `ofEdges? n`: both endpoints in range, no loops. -/
@[expose] def validEdge (n : Nat) (e : Nat × Nat) : Bool :=
  decide (e.1 < n) && decide (e.2 < n) && (e.1 != e.2)

/-- Checked edge-list builder. Returns `none` when some listed edge has an
endpoint out of range or is a loop; otherwise builds the graph whose edges
are the listed unordered pairs, collapsing duplicates in either
orientation. -/
@[expose] def ofEdges? (n : Nat) (edges : List (Nat × Nat)) : Option (Graph n) :=
  if h : edges.all (validEdge n) then
    some <| ofAdj (edgeListAdj edges) (edgeListAdj_symm edges) fun i => by
      rw [edgeListAdj, List.any_eq_false]
      rintro e he
      have hv := (List.all_eq_true.mp h) e he
      rw [validEdge, Bool.and_eq_true, Bool.and_eq_true] at hv
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, not_or, not_and]
      exact ⟨fun h1 h2 => absurd (h1.trans h2.symm) (bne_iff_ne.mp hv.2),
        fun h1 h2 => absurd (h1.trans h2.symm) (bne_iff_ne.mp hv.2)⟩
  else
    none

/-- `ofEdges?` succeeds exactly on well-formed inputs. -/
theorem isSome_ofEdges? (n : Nat) (edges : List (Nat × Nat)) :
    (ofEdges? n edges).isSome = edges.all (validEdge n) := by
  rw [ofEdges?]
  split <;> simp_all

/-- The graph built by `ofEdges?` has exactly the listed undirected edges. -/
theorem adj_ofEdges? {n : Nat} {edges : List (Nat × Nat)} {G : Graph n}
    (h : ofEdges? n edges = some G) (i j : Fin n) :
    G.adj i j = ((i.val, j.val) ∈ edges || (j.val, i.val) ∈ edges) := by
  rw [ofEdges?] at h
  split at h
  · injection h with h
    subst h
    rw [adj_ofAdj, Bool.eq_iff_iff, edgeListAdj, List.any_eq_true]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨a, b⟩, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · subst h1; subst h2; exact Or.inl he
      · subst h1; subst h2; exact Or.inr he
    · rintro (he | he)
      · exact ⟨_, he, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, he, Or.inr ⟨rfl, rfl⟩⟩
  · simp at h

/-! # Neighbours and degrees -/

/-- The sorted duplicate-free array of neighbours of `i`. `O(n)` adjacency
reads; the order is increasing vertex order. -/
@[expose] def nbrs (G : Graph n) (i : Fin n) : Array (Fin n) :=
  ((List.finRange n).filter fun j => G.adj i j).toArray

theorem mem_nbrs {G : Graph n} {i j : Fin n} : j ∈ G.nbrs i ↔ G.adj i j = true := by
  rw [nbrs, List.mem_toArray, List.mem_filter]
  simp [List.mem_finRange]

/-- The degree of a vertex. -/
@[expose] def degree (G : Graph n) (i : Fin n) : Nat :=
  (G.nbrs i).size

/-! # Relabelling -/

/-- Relabel a graph along a vertex map: `(G.relabel f).adj i j = G.adj (f i) (f j)`.
For a bijective `f` this is relabelling by the inverse bijection; stated for
an arbitrary map because neither invariant needs injectivity. -/
@[expose] def relabel (G : Graph n) (f : Fin n → Fin n) : Graph n :=
  ofAdj (fun i j => G.adj (f i) (f j))
    (fun i j => G.adj_symm (f i) (f j))
    (fun i => G.adj_self (f i))

/-- The adjacency correspondence for relabelling. -/
@[simp] theorem adj_relabel (G : Graph n) (f : Fin n → Fin n) (i j : Fin n) :
    (G.relabel f).adj i j = G.adj (f i) (f j) :=
  adj_ofAdj ..

@[simp] theorem relabel_id (G : Graph n) : G.relabel id = G := by
  ext i j
  rw [adj_relabel, id, id]

theorem relabel_relabel (G : Graph n) (f g : Fin n → Fin n) :
    (G.relabel f).relabel g = G.relabel (f ∘ g) := by
  ext i j
  rw [adj_relabel, adj_relabel, adj_relabel, Function.comp, Function.comp]

end Graph

end Hex
