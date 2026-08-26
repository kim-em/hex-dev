/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolySmith.Smith

public section

/-!
Convenience entry points for diagonal polynomial matrices.

These functions deliberately use the general, certified Smith reduction. A
previous adjacent-comparator implementation performed a complete `2 × 2`
Smith reduction at every comparator and then validated dense inverse products;
that path was consistently slower than general elimination. Keeping this
convenience API gives callers a stable surface and leaves room for a future
directly proved gcd/lcm network.
-/

namespace Hex.PolyMatrix

universe u

open Hex

/-- Full Smith data for a diagonal polynomial matrix. -/
@[expose]
def snfDiagonalData {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {r : Nat} (d : Vector (DensePoly F) r) : SmithData F r r :=
  snfData (Matrix.diagMatrix d r r)

/-- Smith-normal matrix for diagonal polynomial input. -/
@[expose]
def snfDiagonal {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {r : Nat} (d : Vector (DensePoly F) r) : Matrix (DensePoly F) r r :=
  snf (Matrix.diagMatrix d r r)

end Hex.PolyMatrix
