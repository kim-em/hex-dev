/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIsoMathlib.AutGroup
public import HexGraphIso.Sparse.Autos
public import Mathlib.Data.List.FinRange
public import Mathlib.SetTheory.Cardinal.Finite
import all HexGraphIso.Sparse.Autos
import all HexGraphIso.Generated
import all HexGraphIso.Nauty.Invariant.OrbitComplete

public section

namespace Hex.GraphIso.Sparse.Aut

variable {n k : Nat}

/-- The full native colour-preserving automorphism subgroup. The dense
interpretation here is a proof bridge and performs no graph search. -/
@[expose] def group (G : Colored n k) : Subgroup (Perm n) := GraphIso.Aut.group G.toDense

@[simp] theorem mem_group (G : Colored n k) (p : Perm n) : p ∈ group G ↔ IsIso G G p :=
  isIso_toDense G G p

/-- The generators emitted by one sparse traversal generate the full
automorphism subgroup, including for the empty graph. -/
theorem closure_eq_group (G : Colored n k) : Subgroup.closure {p | p ∈ gens G} = group G := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro p hp
    exact (mem_group G p).mpr (gens_isIso hp)
  · intro p hp
    have hh := complete G ((mem_group G p).mp hp)
    exact hh.induction (Subgroup.one_mem _) (fun _ hm => Subgroup.subset_closure hm)
      (fun _ _ hp hq => Subgroup.mul_mem _ hp hq) (fun _ hp => Subgroup.inv_mem _ hp)

theorem mem_orbit (G : Colored n k) (u v : Fin n) :
    v ∈ MulAction.orbit (group G) u ↔ SameOrbit G u v := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.val, (mem_group G p.val).mp p.property, hp⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨⟨p, (mem_group G p).mpr hp⟩, he⟩

/-- The actual least representatives identify the full automorphism
orbit quotient with the vertices counted by the native orbit counter. -/
noncomputable def orbitEquiv (G : Colored n k) :
    MulAction.orbitRel.Quotient (group G) (Fin n) ≃
      {v : Fin n // (orbits G)[v.val]! = v.val} where
  toFun := Quotient.lift
    (fun v => ⟨⟨(orbits G)[v.val]!, orbits_lt G v.isLt⟩, orbits_flat G v.val v.isLt⟩)
    (fun u v h => by
      apply Subtype.ext
      apply Fin.ext
      have ho := (mem_orbit G v u).mp (MulAction.orbitRel_apply.mp h)
      exact ((orbits_eq_iff_sameOrbit G v u).mpr ho).symm)
  invFun v := Quotient.mk _ v.val
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h v =>
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      apply (mem_orbit G v _).mpr
      exact sameOrbit_orbits G v
  right_inv := by
    intro v
    apply Subtype.ext
    apply Fin.ext
    exact v.property

private theorem count_card (f : Nat → Bool) :
    (List.range n).countP f = Fintype.card {v : Fin n // f v.val = true} := by
  rw [List.countP_eq_length_filter]
  have hmap : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem <;> simp
  rw [← hmap, List.filter_map, List.length_map]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  symm
  apply Fintype.card_of_subtype
  intro v
  simp

/-- The orbit count stored by the executed sparse traversal is exactly
the cardinality of the full automorphism orbit quotient. -/
theorem numOrbits_card (G : Colored n k) :
    numOrbits G = Nat.card (MulAction.orbitRel.Quotient (group G) (Fin n)) := by
  rw [Nat.card_congr (orbitEquiv G), Nat.card_eq_fintype_card, numOrbits_eq_count, count_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun _ => beq_iff_eq)

end Hex.GraphIso.Sparse.Aut
