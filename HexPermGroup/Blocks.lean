/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Blocks.Build
public import HexPermGroup.Subgroup

public section

namespace Hex.PermGroup

/-- Preservation by symmetric generators extends to the entire group, in
both directions. This applies to arbitrary relations, not only partitions. -/
theorem Blocks.Invariant.generated {S : Array (Perm n)} {R : Fin n → Fin n → Prop}
    (hS : ∀ s ∈ S, s.inv ∈ S) (hR : Blocks.Invariant S R)
    {g : Perm n} (hg : Generated S g) (x y : Fin n) :
    R x y ↔ R (g.get x) (g.get y) := by
  induction hg generalizing x y with
  | id => simp
  | @generator g hg =>
    refine ⟨hR g hg x y, ?_⟩
    intro h
    simpa using hR g.inv (hS g hg) _ _ h
  | @comp g h _ _ hg hh =>
    simpa only [Perm.get_comp] using (hh x y).trans (hg (h.get x) (h.get y))
  | @inv g _ hg => simpa using (hg (g.inv.get x) (g.inv.get y)).symm

namespace Partition

/-- Every represented group element permutes the blocks. -/
@[expose] def IsInvariant (p : Partition n) (G : Group n) : Prop :=
  ∀ g, Generated G.generators g → ∀ x y, p.Same x y ↔ p.Same (g.get x) (g.get y)

/-- Check the complete chain's symmetric generators on block representatives. -/
@[expose] def isInvariant (p : Partition n) (G : Group n) : Bool :=
  Blocks.checkInvariant G.chain.generators p

theorem isInvariant_iff (p : Partition n) (G : Group n) :
    p.isInvariant G = true ↔ p.IsInvariant G := by
  rw [isInvariant, Blocks.checkInvariant_iff]
  constructor
  · intro h g hg x y
    exact h.generated G.chain_symmetric ((G.chain_generated g).mpr hg) x y
  · intro h s hs x y hxy
    exact (h s ((G.chain_generated s).mp (.generator hs)) x y).mp hxy

end Partition

namespace Group

/-- A seeded minimal block system and its forced-union certificate. The checked
chain supplies symmetric generators without recomputing normalization. -/
@[expose] def blocksCert (G : Group n) (pairs : List (Fin n × Fin n)) :
    Blocks.Solution G.chain.generators pairs :=
  Blocks.solve G.chain.generators pairs

/-- Least invariant equivalence relation containing the independent input pairs. -/
@[expose] def blocks (G : Group n) (pairs : List (Fin n × Fin n)) : Partition n :=
  (G.blocksCert pairs).partition

theorem blocks_invariant (G : Group n) (pairs : List (Fin n × Fin n)) :
    (G.blocks pairs).IsInvariant G := by
  intro g hg x y
  exact (G.blocksCert pairs).admissible.invariant.generated G.chain_symmetric
    ((G.chain_generated g).mpr hg) x y

theorem blocks_seeds (G : Group n) (pairs : List (Fin n × Fin n))
    (q : Fin n × Fin n) (hq : q ∈ pairs) : (G.blocks pairs).Same q.1 q.2 :=
  (G.blocksCert pairs).admissible.seeds q hq

/-- Minimality among all invariant equivalence relations, including relations
not supplied as a canonical partition. -/
theorem blocks_least (G : Group n) (pairs : List (Fin n × Fin n))
    (R : Fin n → Fin n → Prop) (hR : Equivalence R)
    (hG : ∀ g, Generated G.generators g → ∀ x y, R x y → R (g.get x) (g.get y))
    (hs : ∀ q ∈ pairs, R q.1 q.2) : (G.blocks pairs).Refines R :=
  (G.blocksCert pairs).least R ⟨hR,
    fun s hs => hG s ((G.chain_generated s).mp (.generator hs)), hs⟩

@[simp] theorem blocks_empty (G : Group n) : G.blocks [] = Partition.discrete n := by
  apply Partition.ext
  intro x y
  rw [Partition.discrete_same]
  constructor
  · exact G.blocks_least [] Eq ⟨Eq.refl, Eq.symm, Eq.trans⟩
      (fun g _ _ _ h => congrArg g.get h) (by simp) x y
  · intro h
    exact h ▸ rfl

/-- Joining every point to one point forces the indiscrete partition. -/
theorem blocks_star (G : Group n) (a : Fin n) :
    G.blocks ((List.finRange n).map fun b => (a, b)) = Partition.indiscrete n := by
  apply Partition.ext
  intro x y
  constructor
  · intro _
    exact Partition.indiscrete_same x y
  · intro _
    have hx := G.blocks_seeds ((List.finRange n).map fun b => (a, b))
      (a, x) (List.mem_map.mpr ⟨x, by simp, rfl⟩)
    have hy := G.blocks_seeds ((List.finRange n).map fun b => (a, b))
      (a, y) (List.mem_map.mpr ⟨y, by simp, rfl⟩)
    exact hx.symm.trans hy

end Group

end Hex.PermGroup
