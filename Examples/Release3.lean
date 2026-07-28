/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.IrreducibilityElab
public meta import HexBerlekampZassenhaus.FactorProvider
public import HexBerlekamp.IrreducibilityElab
public import HexBerlekampZassenhaus.FactorProvider

public section

/-!
# Release 3: certified integer factorization

The input has factors with coefficients much larger than the small modular
prime used to discover them, so the production Berlekamp--Zassenhaus path must
lift modular information before reconstructing the integer factors.  The
elaborator performs untrusted search, then emits kernel-checked product and
irreducibility certificates.
-/

namespace Examples.Release3

open Hex

/-- `(x + 1000)²(x - 2003)(x² + 1)`, with a repeated linear factor. -/
def input : ZPoly :=
  DensePoly.ofCoeffs #[1000, 1] * DensePoly.ofCoeffs #[-2003, 1] *
    DensePoly.ofCoeffs #[1, 0, 1] * DensePoly.ofCoeffs #[1000, 1]

/-- The release-facing total factorization result. -/
noncomputable def result := factor_poly input

example : result.scalar = 1 := rfl

example : result.factors.length = 4 := rfl

/-- The result carries an exact reconstruction equation. -/
example : DensePoly.C result.scalar * result.factors.prod = input :=
  result.factors_mul

/-- Every emitted polynomial factor comes with a checked irreducibility
certificate; clients do not need to trust the search implementation. -/
example : ∀ q ∈ result.factors, ZPoly.Irreducible q :=
  result.factors_irred

end Examples.Release3
