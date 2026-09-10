/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Check

public section

namespace Hex.PermGroup.Search.Certificate

/-- Number of nodes in a completeness certificate, including its root. -/
@[expose] def nodes (certificate : Certificate Reason) : Nat :=
  match certificate with
  | .branch children => 1 + (children.toList.map nodes).sum
  | .rejected _ | .covered | .leaf => 1
decreasing_by
  all_goals
    have h := List.sizeOf_lt_of_mem ‹_ ∈ children.toList›
    cases children
    simp_all
    omega

end Hex.PermGroup.Search.Certificate
