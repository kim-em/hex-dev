/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecMax
public import HexGraphIso.Nauty.Sparse.SpecNode

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The scalar maximum of an existing unpruned leaf list. The empty case
only totalizes this specification helper; sufficient-fuel theorems prove
that every valid subtree used in the production proof has an attaining leaf. -/
@[expose] def SpecLeaf.maximum (G : Hex.SparseGraph n) : List (SpecLeaf n) → Key n
  | [] => ⟨[], G⟩
  | first :: rest => (best G first rest).key G

theorem SpecLeaf.maximum_attains (G : Hex.SparseGraph n) {leaves : List (SpecLeaf n)}
    (hne : leaves ≠ []) : ∃ leaf ∈ leaves, leaf.key G = maximum G leaves := by
  cases leaves with
  | nil => exact (hne rfl).elim
  | cons first rest => exact ⟨best G first rest, best_mem G first rest, rfl⟩

theorem SpecLeaf.maximum_bound (G : Hex.SparseGraph n) {leaves : List (SpecLeaf n)}
    {leaf : SpecLeaf n} (hm : leaf ∈ leaves) : Key.Le (leaf.key G) (maximum G leaves) := by
  cases leaves with
  | nil => cases hm
  | cons first rest => exact best_bound G first rest leaf hm

/-- Leaf transport gives an inequality between subtree maxima, without
requiring that the two enumerations use the same order or have unique keys. -/
theorem SpecLeaf.maximum_le {G H : Hex.SparseGraph n} {left right : List (SpecLeaf n)}
    (hne : left ≠ [])
    (hm : ∀ leaf ∈ left, ∃ other ∈ right, other.key H = leaf.key G) :
    Key.Le (maximum G left) (maximum H right) := by
  obtain ⟨leaf, hl, he⟩ := maximum_attains G hne
  obtain ⟨other, hr, hk⟩ := hm leaf hl
  rw [← he, ← hk]
  exact maximum_bound H hr

/-- The native unpruned subtree's maximum. This aggregates `specLeaves`
and introduces no alternate refinement or production search. -/
@[expose] def subtreeKey (G : Hex.SparseGraph n) (tcLevel fuel level : Nat)
    (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) : Key n :=
  SpecLeaf.maximum G (specLeaves G tcLevel fuel level lab ptn active numcells)

/-- Every sufficiently fueled valid subtree has a literal attaining leaf. -/
theorem SpecNode.key_attains {G : Hex.SparseGraph n} {tcLevel fuel level numcells : Nat}
    {lab ptn : Array Nat} {active : VSet n} (h : SpecNode G level lab ptn active numcells)
    (hf : n < fuel + numcells) :
    ∃ leaf ∈ specLeaves G tcLevel fuel level lab ptn active numcells,
      leaf.key G = subtreeKey G tcLevel fuel level lab ptn active numcells :=
  SpecLeaf.maximum_attains G
    (specLeaves_nonempty G tcLevel fuel level lab ptn active numcells h.label h.node h.count h.depth hf)

theorem subtreeKey_bound {G : Hex.SparseGraph n} {tcLevel fuel level numcells : Nat}
    {lab ptn : Array Nat} {active : VSet n} {leaf : SpecLeaf n}
    (hm : leaf ∈ specLeaves G tcLevel fuel level lab ptn active numcells) :
    Key.Le (leaf.key G) (subtreeKey G tcLevel fuel level lab ptn active numcells) :=
  SpecLeaf.maximum_bound G hm

/-- The scalar maximum agrees with the existing root declaration and its
attaining-label definition, including the special empty graph leaf. -/
theorem root_maximum (G : GraphIso.Sparse.Colored n k) :
    SpecLeaf.maximum G.graph (rootLeaves G) = canonSpecKey G := by
  have he := List.cons_head_tail (rootLeaves_nonempty G)
  conv => lhs; rw [← he]
  rfl

end Hex.GraphIso.Nauty.Sparse
