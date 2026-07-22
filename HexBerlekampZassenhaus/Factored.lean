/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZ.Core
public import HexPoly.Euclid
public import HexBerlekampZassenhaus.IrreducibleCore

public section

/-!
The result type of the `factor_poly` term elaborator for `Hex.ZPoly`; see
`HexBerlekamp/Factored.lean` for the `FpPoly` counterpart and the generator
conventions.
-/

namespace Hex

/-- A certified irreducible factorization of `f : ZPoly`: a scalar (the
signed content) and a factor list (with repetition) whose product
reconstructs `f`, every listed factor irreducible in the element sense of
`ℤ[X]`. Produced by the `factor_poly` elaborator with primitive
positive-leading-coefficient factors. -/
structure ZPoly.Factored (f : ZPoly) where
  /-- The scalar (the signed content for nonzero `f`). -/
  scalar : Int
  /-- The irreducible factors, with repetition (primitive, positive leading
  coefficient, by generator convention). -/
  factors : List ZPoly
  /-- The scalar times the factor product reconstructs `f`. -/
  factors_mul : DensePoly.C scalar * factors.prod = f
  /-- Every listed factor is irreducible. -/
  factors_irred : ∀ q ∈ factors, ZPoly.Irreducible q

end Hex
