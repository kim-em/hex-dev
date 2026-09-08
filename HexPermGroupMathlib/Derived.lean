/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.Derived
public import HexPermGroupMathlib.Normal
public import Mathlib.GroupTheory.Commutator.Basic

public section

open scoped commutatorElement

namespace Hex.Perm

@[simp] theorem toEquiv_comm (p q : Perm n) : (p.comm q).toEquiv = ⁅p.toEquiv, q.toEquiv⁆ := by
  simp [comm, commutatorElement_def, mul_assoc]

end Hex.Perm

namespace Hex.PermGroup.Group

/-- The checked derived group is the mathematical commutator subgroup of the
ambient generated subgroup, with the original action degree retained. -/
theorem derived_spec (G : Group n) :
    closure G.derived.generators = ⁅closure G.generators, closure G.generators⁆ := by
  apply le_antisymm
  · intro e he
    have hp : Derived.Member G (Perm.ofEquiv e) := (G.mem_derived _).mp
      (generated_iff_mem.mpr (by simpa using he))
    suffices ∀ p, Derived.Member G p → p.toEquiv ∈ ⁅closure G.generators, closure G.generators⁆ by
      simpa using this _ hp
    intro p hp
    induction hp with
    | id => simp
    | comm hp hq =>
      simpa using Subgroup.commutator_mem_commutator (generated_iff_mem.mp hp) (generated_iff_mem.mp hq)
    | comp _ _ ip iq => simpa using (⁅closure G.generators, closure G.generators⁆).mul_mem ip iq
    | inv _ ip => simpa using (⁅closure G.generators, closure G.generators⁆).inv_mem ip
  · apply Subgroup.commutator_le.mpr
    intro p hp q hq
    have hp' : Generated G.generators (Perm.ofEquiv p) := generated_iff_mem.mpr (by simpa using hp)
    have hq' : Generated G.generators (Perm.ofEquiv q) := generated_iff_mem.mpr (by simpa using hq)
    simpa using generated_iff_mem.mp (G.comm_mem_derived _ _ hp' hq')

end Hex.PermGroup.Group
