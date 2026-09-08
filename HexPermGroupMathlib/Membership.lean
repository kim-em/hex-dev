/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Membership
public import HexPermGroupMathlib.Subgroup

public section

namespace Hex.PermGroup.Group

/-- Membership programs exist exactly for the corresponding Mathlib subgroup. -/
theorem word?_spec (G : Group n) (p : Perm n) :
    (∃ w : Program, G.word? p = some w ∧ checkWord G.generators p w = true) ↔
      p.toEquiv ∈ closure G.generators := by
  rw [word?_complete, generated_iff_mem]

/-- Containment certificates decide inclusion of the corresponding subgroups. -/
theorem subgroupWords?_spec (H G : Group n) :
    (H.subgroupWords? G).isSome = true ↔ closure H.generators ≤ closure G.generators := by
  rw [subgroupWords?_isSome, isSubgroup_spec]

end Hex.PermGroup.Group
