/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIsoMathlib.AutGroup
public import Mathlib.Data.List.FinRange
public import Mathlib.SetTheory.Cardinal.Finite
import HexGraphIso.AutGroup
import all HexGraphIso.Autos
import all HexGraphIso.Nauty.Invariant.OrbitComplete

public section

namespace Hex.GraphIso.Aut

variable {n k : Nat}

private theorem count_card (f : Nat → Bool) :
    ((List.range n).filter f).length = Fintype.card {v : Fin n // f v.val = true} := by
  have hmap : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem <;> simp
  rw [← hmap, List.filter_map, List.length_map]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  symm
  apply Fintype.card_of_subtype
  intro v
  simp

/-- The reported orbit length is the cardinality of the full group-action orbit. -/
theorem orbitSize_card (G : Colored n k) (v : Fin n) :
    orbitSize G v = Nat.card (MulAction.orbit (group G) v) := by
  classical
  let _ := Fintype.ofFinite (MulAction.orbit (group G) v)
  rw [orbitSize, sizeAt, count_card, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro u
  rw [beq_iff_eq, orbits_eq_iff_sameOrbit, mem_orbit]
  exact ⟨SameOrbit.symm, SameOrbit.symm⟩

/-- Choosing the stored representative identifies the orbit quotient
with precisely the vertices counted by `numOrbits`. -/
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

/-- The reported orbit count is the cardinality of the full automorphism
orbit quotient. -/
theorem numOrbits_card (G : Colored n k) :
    numOrbits G = Nat.card (MulAction.orbitRel.Quotient (group G) (Fin n)) := by
  rw [Nat.card_congr (orbitEquiv G), Nat.card_eq_fintype_card, numOrbits, countRoots, count_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun _ => beq_iff_eq)

end Hex.GraphIso.Aut
