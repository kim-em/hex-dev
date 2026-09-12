/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Rows
public import HexGraphIso.Nauty.Sparse.Inverse
public import HexGraphIso.Sparse.Iso
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Canonical row installation changes entries in the allocated arrays;
it does not resize either array, including when installing only a suffix. -/
theorem updatecan_sizes (g : Graph n) (R : Rows n) (lab : Array Nat) (samerows : Nat) :
    (updatecan g R lab samerows).offsets.size = R.offsets.size ∧
      (updatecan g R lab samerows).neighbors.size = R.neighbors.size := by
  unfold updatecan
  apply Id.of_wp_run_eq rfl (fun r : Rows n =>
    r.offsets.size = R.offsets.size ∧ r.neighbors.size = R.neighbors.size)
  mvcgen invariants
  | inv1 => ⇓⟨_, s⟩ => ⌜s.1.size = R.offsets.size ∧ s.2.1.size = R.neighbors.size⌝
  | inv2 => ⇓⟨_, s⟩ => ⌜s.1.size = R.neighbors.size⌝
  with grind

/-- The diagnostic comparison always reports a prefix length at most `n`.
Semantic correctness of those rows additionally requires a valid store. -/
theorem testcanlab_bound (g : Graph n) (R : Rows n) (lab : Array Nat) :
    (testcanlab g R lab).2 ≤ n := by
  unfold testcanlab
  apply Id.of_wp_run_eq rfl (fun r : Int × Nat => r.2 ≤ n)
  mvcgen invariants
  | inv1 => ⇓⟨_, s⟩ => ⌜∀ r, s.1 = some r → r.2 ≤ n⌝
  | inv2 => ⇓⟨_, _⟩ => ⌜True⌝
  | inv3 => ⇓⟨_, _⟩ => ⌜True⌝
  | inv4 => ⇓⟨_, s⟩ => ⌜∀ r, s.1 = some r → r.2 ≤ n⌝
  with grind

/-- Breadth-first distances use a fixed array with one slot per vertex. -/
@[simp] theorem distvals_size (g : Graph n) (root : Nat) : (distvals g root).size = n := by
  unfold distvals
  apply Id.of_wp_run_eq rfl (fun a : Array Nat => a.size = n)
  mvcgen invariants
  | inv1 => ⇓⟨_, s⟩ => ⌜s.1.size = n⌝
  | inv2 => ⇓⟨_, s⟩ => ⌜s.1.size = n⌝
  with grind

/-- In an undirected graph it suffices to check the rows of moved
vertices. Edges incident to a fixed vertex are covered by their other end;
an edge with both endpoints fixed is unchanged. -/
theorem autom_iff_moved (G : Hex.SparseGraph n) (p : Perm n) :
    (∀ i j, G.adj (p.get i) (p.get j) = G.adj i j) ↔
      ∀ i, p.get i ≠ i → ∀ j, G.adj (p.get i) (p.get j) = G.adj i j := by
  refine ⟨fun h i _ j => h i j, ?_⟩
  intro h i j
  by_cases hi : p.get i = i
  · by_cases hj : p.get j = j
    · rw [hi, hj]
    · rw [G.adj_symm (p.get i) (p.get j), h j hj i, G.adj_symm j i]
  · exact h i hi j

end Hex.GraphIso.Nauty.Sparse
