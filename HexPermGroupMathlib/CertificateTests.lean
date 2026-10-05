/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
import HexPermGroupMathlib
meta import HexPermGroup.CertificateTests

open Hex Hex.PermGroup
namespace Hex.PermGroup.Mathlib.CertificateTests
#replay_perm_group_certificate images for
  ({Kernel.permOfImages 3 [1, 2, 0], Kernel.permOfImages 3 [1, 0, 2]} :
    Set (Equiv.Perm (Fin 3)))
#replay_perm_group_certificate finset for
  (↑({Kernel.permOfImages 3 [1, 2, 0], Kernel.permOfImages 3 [1, 0, 2]} :
    Finset (Equiv.Perm (Fin 3))))
#replay_perm_group_certificate fallback for
  ({Kernel.permOfImages 3 [0, 0, 1]} : Set (Equiv.Perm (Fin 3)))
example : Nat.card (Subgroup.closure
    ({Kernel.permOfImages 3 [0, 0, 1]} : Set (Equiv.Perm (Fin 3)))) = 1 := by
  perm_group
example : Nat.card (Subgroup.closure
    {x : Equiv.Perm (Fin 3) | x ∈ [Kernel.permOfImages 3 [1, 2, 0]]}) = 3 := by
  perm_group
example : Kernel.permOfImages 3 [1, 0, 2] ∉ Subgroup.closure
    ((fun x : Equiv.Perm (Fin 3) => x ∈ [Kernel.permOfImages 3 [1, 2, 0]]) : Set _) := by
  perm_group

-- The previous certificate emitter used these assembly lemmas.
example : Nat.card (Subgroup.closure
    {x : Equiv.Perm (Fin 0) | x ∈ [(1 : Equiv.Perm (Fin 0))]}) = 1 := by
  have hS := Kernel.map_pack_cons
    (show Kernel.pack (Perm.ofEquiv (1 : Equiv.Perm (Fin 0))) = 0 by decide +kernel)
    (Kernel.map_pack_nil (n := 0))
  exact Kernel.card_of_check hS (show Kernel.check 0 [0] [] = true by decide +kernel) rfl

-- Preserve diagnostics once the Mathlib goal shape is recognized.
/--
error: perm_group: the claimed order must be a numeral
  N
-/
#guard_msgs in
example (N : Nat) : Nat.card (Subgroup.closure
    ({Kernel.permOfImages 3 [1, 2, 0]} : Set (Equiv.Perm (Fin 3)))) = N := by
  perm_group
end Hex.PermGroup.Mathlib.CertificateTests
