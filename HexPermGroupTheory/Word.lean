/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Word
public import HexPermGroupTheory.Generated
public import HexPermGroupTheory.Perm
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace Hex.PermGroup

/-- A successfully replayed word proves membership in Mathlib's subgroup. -/
theorem checkWord_spec {S : Array (Perm n)} {p : Perm n} {program : Program}
    (h : checkWord S p program = true) : p.toEquiv ∈ closure S :=
  generated_iff_mem.mp (checkWord_sound h)

end Hex.PermGroup
