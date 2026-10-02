/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIsoMathlib.Sparse.AutGroup
public import Mathlib.GroupTheory.GroupAction.Quotient
import all HexGraphIso.Generated
import all HexGraphIso.Orbit

public section

namespace Hex.GraphIso.Sparse.Aut

variable {n k : Nat}

/-- The full native automorphism group fixing the actual individualized
base. This is a semantic subgroup, with no additional graph search. -/
def stabilizer (G : Colored n k) (base : List (Fin n)) : Subgroup (Perm n) where
  carrier := {p | IsIso G G p ∧ Perm.Fixes base p}
  one_mem' := ⟨IsIso.refl G, Perm.Fixes.id base⟩
  mul_mem' hp hq := ⟨hq.1.trans hp.1, hp.2.comp hq.2⟩
  inv_mem' hp := ⟨hp.1.symm, hp.2.inv⟩

@[simp] theorem mem_stabilizer (G : Colored n k) (base : List (Fin n)) (p : Perm n) :
    p ∈ stabilizer G base ↔ IsIso G G p ∧ Perm.Fixes base p := Iff.rfl

theorem stabilizer_nil (G : Colored n k) : stabilizer G [] = group G := by
  ext p
  simp only [mem_stabilizer, mem_group]
  exact ⟨And.left, fun hp => ⟨hp, Perm.Fixes.nil p⟩⟩

theorem mem_stabilizer_orbit (G : Colored n k) (base : List (Fin n)) (u v : Fin n) :
    v ∈ MulAction.orbit (stabilizer G base) u ↔ GraphIso.Aut.Orbit G.toDense base u v := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.val, (isIso_toDense G G p.val).mpr p.property.1, p.property.2, hp⟩
  · rintro ⟨p, hp, hf, he⟩
    exact ⟨⟨p, (isIso_toDense G G p).mp hp, hf⟩, he⟩

/-- Adding the next first-path vertex to the base gives the ordinary
point stabilizer of the preceding full stabilizer. -/
def stabilizerEquiv (G : Colored n k) (base : List (Fin n)) (v : Fin n) :
    MulAction.stabilizer (stabilizer G base) v ≃ stabilizer G (v :: base) where
  toFun p := ⟨p.val.val, p.val.property.1, Perm.Fixes.cons.mpr ⟨p.property, p.val.property.2⟩⟩
  invFun p := ⟨⟨p.val, p.property.1, (Perm.Fixes.cons.mp p.property.2).2⟩,
    (Perm.Fixes.cons.mp p.property.2).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite-vertex count used in the native index theorem is the
cardinality of the corresponding full stabilizer orbit. -/
theorem stabilizer_orbit_card (G : Colored n k) (base : List (Fin n)) (v : Fin n)
    [DecidablePred (GraphIso.Aut.Orbit G.toDense base v)] :
    (List.finRange n).countP (fun w => decide (GraphIso.Aut.Orbit G.toDense base v w)) =
      Nat.card (MulAction.orbit (stabilizer G base) v) := by
  classical
  have he : MulAction.orbit (stabilizer G base) v ≃
      {w : Fin n // GraphIso.Aut.Orbit G.toDense base v w} :=
    Equiv.subtypeEquivRight (mem_stabilizer_orbit G base v)
  rw [Nat.card_congr he, Nat.card_eq_fintype_card, List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  symm
  apply Fintype.card_of_subtype
  intro w
  simp

/-- Orbit–stabilizer for precisely the individualized base and guide
whose index the sparse executable multiplies into its accumulator. -/
theorem stabilizer_card (G : Colored n k) (base : List (Fin n)) (v : Fin n)
    [DecidablePred (GraphIso.Aut.Orbit G.toDense base v)] :
    Nat.card (stabilizer G base) = Nat.card (stabilizer G (v :: base)) *
      (List.finRange n).countP (fun w => decide (GraphIso.Aut.Orbit G.toDense base v w)) := by
  rw [stabilizer_orbit_card, Nat.mul_comm, ← Nat.card_congr (stabilizerEquiv G base v),
    ← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (stabilizer G base) v)]

end Hex.GraphIso.Sparse.Aut
