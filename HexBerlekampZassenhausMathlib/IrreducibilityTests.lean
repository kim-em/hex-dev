/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib

public section

/-!
# Integer polynomial irreducibility API tests

These checks ensure that importing the package exposes the advertised
correspondence between executable and Mathlib irreducibility at the root
`Hex.ZPoly` namespace.
-/

#check Hex.ZPoly.Irreducible_iff_polynomialIrreducible
#check Hex.ZPoly.polynomialIrreducible_iff_irreducible
#check Hex.ZPoly.isIrreducible_iff

example (f : Hex.ZPoly) : Decidable (Hex.ZPoly.Irreducible f) :=
  inferInstance
