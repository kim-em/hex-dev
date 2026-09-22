/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturm.Basic

public section

namespace Hex.SignDet

/-- The unreduced moment product, with empty product and every zeroth power
one. Replay validates lengths and exponent ranges before using it. -/
@[expose] def moment {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Mul E]
    (qs : List (DensePoly E)) (e : List Nat) : DensePoly E :=
  ((qs.zip e).map fun (q, k) => q.natPow k).foldl (· * ·) 1

end Hex.SignDet
