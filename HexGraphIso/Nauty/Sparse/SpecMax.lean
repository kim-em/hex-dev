/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecBound

public section

namespace Hex.GraphIso.Nauty.Sparse

namespace SpecLeaf

/-- Retain an attaining label while comparing the full sparse keys. -/
@[expose] def max (G : Hex.SparseGraph n) (a b : SpecLeaf n) : SpecLeaf n :=
  if Key.cmp (a.key G) (b.key G) = .lt then b else a

theorem max_mem (G : Hex.SparseGraph n) (a b : SpecLeaf n) :
    max G a b = a ∨ max G a b = b := by
  unfold max
  split <;> simp

theorem key_max (G : Hex.SparseGraph n) (a b : SpecLeaf n) :
    (max G a b).key G = Key.max (a.key G) (b.key G) := by
  unfold max Key.max
  split <;> rfl

/-- The first greatest leaf in enumeration order. -/
@[expose] def best (G : Hex.SparseGraph n) (first : SpecLeaf n) (rest : List (SpecLeaf n)) : SpecLeaf n :=
  rest.foldl (max G) first

theorem best_mem (G : Hex.SparseGraph n) (first : SpecLeaf n) (rest : List (SpecLeaf n)) :
    best G first rest ∈ first :: rest := by
  induction rest generalizing first with
  | nil => simp [best]
  | cons next rest ih =>
    change best G (max G first next) rest ∈ first :: next :: rest
    rcases List.mem_cons.mp (ih (max G first next)) with he | hm
    · rw [he]
      rcases max_mem G first next with he | he <;> simp [he]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)

theorem best_bound (G : Hex.SparseGraph n) (first : SpecLeaf n) (rest : List (SpecLeaf n)) :
    ∀ leaf ∈ first :: rest, Key.Le (leaf.key G) ((best G first rest).key G) := by
  induction rest generalizing first with
  | nil =>
    intro leaf hm
    have he : leaf = first := by simpa using hm
    subst leaf
    exact Key.le_refl _
  | cons next rest ih =>
    intro leaf hm
    change Key.Le (leaf.key G) ((best G (max G first next) rest).key G)
    have hmax := ih (max G first next) (max G first next) List.mem_cons_self
    rw [key_max] at hmax
    rcases List.mem_cons.mp hm with he | hm
    · rw [he]
      exact Key.le_trans (Key.le_max_left _ _) hmax
    · rcases List.mem_cons.mp hm with he | hm
      · rw [he]
        exact Key.le_trans (Key.le_max_right _ _) hmax
      · exact ih _ _ (List.mem_cons_of_mem _ hm)

end SpecLeaf

/-- A reachable maximum of the complete finite sparse tree. Nonemptiness
supplies the initial candidate without an arbitrary fallback. -/
@[expose] def specBest (G : GraphIso.Sparse.Colored n k) : SpecLeaf n :=
  SpecLeaf.best G.graph ((rootLeaves G).head (rootLeaves_nonempty G)) (rootLeaves G).tail

/-- The sparse declarative maximum, in sparse nauty's own key order. -/
@[expose] def canonSpecKey (G : GraphIso.Sparse.Colored n k) : Key n :=
  (specBest G).key G.graph

/-- A labelling attaining the sparse declarative maximum. -/
@[expose] def canonSpecLabel (G : GraphIso.Sparse.Colored n k) : Label n :=
  (specBest G).label

theorem specBest_mem (G : GraphIso.Sparse.Colored n k) : specBest G ∈ rootLeaves G := by
  have h := SpecLeaf.best_mem G.graph ((rootLeaves G).head (rootLeaves_nonempty G)) (rootLeaves G).tail
  rwa [List.cons_head_tail] at h

theorem canonSpecKey_bound (G : GraphIso.Sparse.Colored n k) {leaf : SpecLeaf n}
    (h : leaf ∈ rootLeaves G) : Key.Le (leaf.key G.graph) (canonSpecKey G) := by
  have hm := SpecLeaf.best_bound G.graph ((rootLeaves G).head (rootLeaves_nonempty G)) (rootLeaves G).tail
  rw [List.cons_head_tail] at hm
  exact hm leaf h

theorem canonSpecLabel_attains (G : GraphIso.Sparse.Colored n k) :
    (canonSpecKey G).graph = G.graph.relabel (canonSpecLabel G).perm := rfl

/-- A reachable upper bound is exactly the declarative maximum. -/
theorem canonSpecKey_eq (G : GraphIso.Sparse.Colored n k) {leaf : SpecLeaf n}
    (hm : leaf ∈ rootLeaves G)
    (hb : ∀ other ∈ rootLeaves G, Key.Le (other.key G.graph) (leaf.key G.graph)) :
    canonSpecKey G = leaf.key G.graph :=
  Key.le_antisymm (hb _ (specBest_mem G)) (canonSpecKey_bound G hm)

end Hex.GraphIso.Nauty.Sparse
