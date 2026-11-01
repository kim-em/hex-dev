/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Division
public import HexGroebner.CheckedBasis

public section

namespace Hex.Groebner

/-- Compute and independently verify the unique normal form against an already
accepted complete basis. Nested division and replay share one allowance. -/
def normalFormWith (basis : CheckedBasis) (budget : Certificate.Budget)
    (target : Certificate.Polynomial) : DivideResult basis.context basis.polynomials target :=
  divideWith basis.context budget basis.polynomials target

end Hex.Groebner
