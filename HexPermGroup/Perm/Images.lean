/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Perm

public section

namespace Hex.Perm

/-- A permutation from its literal image list, with identity as the fallback
for invalid input. `Kernel.ofNatArray_permOfImages` proves this fallback is
unreachable when `Kernel.imagesOk` accepts. -/
@[expose] def ofImages (n : Nat) (l : List Nat) : Perm n :=
  match Perm.ofNatArray? n l.toArray with
  | some p => p
  | none => Perm.id n

/-- The image list, read by the tactic in compiled code. -/
@[expose] def images (p : Perm n) : List Nat :=
  (List.finRange n).map fun i => (p.get i).val

end Hex.Perm

