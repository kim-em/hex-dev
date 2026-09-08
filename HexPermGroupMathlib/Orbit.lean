/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Orbit.Schreier
public import HexPermGroupMathlib.Word
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Action.End

public section

namespace Hex.PermGroup

/-- A checked orbit is the full orbit of Mathlib's generated subgroup. -/
theorem checkOrbit_spec {S : Array (Perm n)} {a : Fin n} {c : Orbit n}
    (h : checkOrbit S a c = true) (x : Fin n) :
    x ∈ c.points ↔ ∃ e : Equiv.Perm (Fin n), e ∈ closure S ∧ e a = x := by
  rw [checkOrbit_sound h]
  constructor
  · rintro ⟨p, hp, hx⟩
    exact ⟨p.toEquiv, generated_iff_mem.mp hp, hx⟩
  · rintro ⟨e, he, hx⟩
    refine ⟨Perm.ofEquiv e, generated_iff_mem.mpr ?_, ?_⟩
    · simpa using he
    · simpa using hx

/-- The Schreier generators describe the subgroup intersection with the ambient
point stabilizer, retaining the declared permutation degree. -/
theorem closure_stabilizerGens {S : Array (Perm n)} {a : Fin n} {c : Orbit n}
    (h : c.Valid S a) :
    closure (Orbit.stabilizerGens h) =
      closure S ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) a := by
  ext e
  have he := Orbit.stabilizerGens_spec h (Perm.ofEquiv e)
  simpa [generated_iff_mem, MulAction.mem_stabilizer_iff] using he

end Hex.PermGroup
