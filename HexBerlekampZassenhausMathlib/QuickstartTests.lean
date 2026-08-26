/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhausMathlib

namespace HexBerlekampZassenhausMathlibQuickstartTests

open Polynomial

#check HexBerlekampZassenhausMathlib.factorize_product
#check HexBerlekampZassenhausMathlib.factorize_normalized
#check HexBerlekampZassenhausMathlib.factorize_unique
#check Hex.ZPoly.Irreducible_iff_polynomialIrreducible

noncomputable def fac :=
  factor_poly ((X - 1) ^ 2 * (X ^ 2 + 1) : Polynomial ℤ)

example : Irreducible (X ^ 4 + 8 * X + 12 : Polynomial ℤ) := by
  irreducibility

end HexBerlekampZassenhausMathlibQuickstartTests
