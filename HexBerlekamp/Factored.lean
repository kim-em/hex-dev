/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp.Field
public import HexPolyFp.Ring
public import HexPoly.Euclid

public section

/-!
The result type of the `factor_poly` term elaborator for `FpPoly p`: a
certified irreducible factorization, destructured as
`obtain ⟨scalar, factors, factors_mul, factors_irred⟩ := factor_poly f`.

The generator emits monic factors in nondecreasing degree order with the
leading unit in `scalar`, and repeats each factor to its multiplicity — but
those normalizations are conventions of the generator, not invariants of this
type; users needing them on the emitted literals can `decide` them.
-/

namespace Hex

/-- A certified irreducible factorization of `f : FpPoly p`: a scalar and a
factor list (with repetition) whose product reconstructs `f`, every listed
factor irreducible. Produced by the `factor_poly` elaborator with monic
factors and the leading unit in `scalar`. -/
structure FpPoly.Factored {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) where
  /-- The unit scalar (the leading coefficient for nonzero `f`). -/
  scalar : ZMod64 p
  /-- The irreducible factors, with repetition (monic by generator
  convention). -/
  factors : List (FpPoly p)
  /-- The scalar times the factor product reconstructs `f`. -/
  factors_mul : DensePoly.C scalar * factors.prod = f
  /-- Every listed factor is irreducible. -/
  factors_irred : ∀ q ∈ factors, FpPoly.Irreducible q

end Hex
