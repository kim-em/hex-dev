/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDet.Basic

public section

/-!
The integer recipe.

`Int` selects fraction-free Bareiss at every `n > 2`, over the native
`HexArith.Int.exactDiv` quotient that `Hex.Matrix.bareiss` already uses. The
identity representation maps mean the runner does no conversion.

This is the initial availability rule from
[hex-det](SPEC/hex-det.md), not a measured claim that Bareiss beats
multi-modular reconstruction at large dimensions: `hex-modular-matrix` has no
implementation yet, so `Hex.Det.IntArm` offers no modular constructor to select.
-/

namespace Hex.Det

/-- The integer recipe: Bareiss on the integer backend, reached through identity
representation maps. -/
instance instDetOpsInt : DetOps Int where
  policy := .integer id id .bareiss

example : (DetOps.policy (R := Int)).arm = Arm.bareiss := rfl

end Hex.Det
