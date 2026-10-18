/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.TransportInventory

public section
namespace Hex.RealClosure.Transport.Inventory.Agreement

variable {E : Type u} {K : Type v} [Zero E]
variable [CommRing K]
variable {read : E → K} {S : E → Prop} {sourceSign : E → Int} {targetSign : K → Int}

/-- The empty inventory imposes no additional condition. -/
theorem nil : Agreement read S sourceSign targetSign [] := by
  intro x member
  cases member

/-- Retain the complete domain, sign and zero-reflection data at the head. -/
theorem cons {x : E} {xs : List E}
    (head : S x ∧ targetSign (read x) = sourceSign x ∧ (read x = 0 ↔ x = 0))
    (tail : Agreement read S sourceSign targetSign xs) :
    Agreement read S sourceSign targetSign (x :: xs) := by
  intro y member
  rcases List.mem_cons.mp member with same | old
  · subst y
    exact head
  · exact tail y old

/-- Combine two finite inventories while preserving their order and duplicates. -/
theorem join {xs ys : List E}
    (left : Agreement read S sourceSign targetSign xs)
    (right : Agreement read S sourceSign targetSign ys) :
    Agreement read S sourceSign targetSign (xs ++ ys) := by
  intro x member
  rcases List.mem_append.mp member with old | old
  · exact left x old
  · exact right x old

end Hex.RealClosure.Transport.Inventory.Agreement
