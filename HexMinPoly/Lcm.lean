/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMinPoly.Order
public import HexPoly.Lcm

public section

/-! The standard-basis least-common-multiple fold. -/

namespace Hex.Matrix

universe u

variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F] {n : Nat}

/-- Fold the order polynomials of all standard basis vectors. -/
@[expose]
def basisOrderLcm (A : Matrix F n n) : DensePoly F :=
  DensePoly.lcmList
    ((List.finRange n).map (fun i => vecMinPoly A (basisVec n i)))

end Hex.Matrix
