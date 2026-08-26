/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.Factorization
public import HexBerlekampZassenhaus.FactorProduct
public import HexBerlekampZassenhaus.IrreducibleDecide
public import HexBerlekampZassenhaus.Factored
public meta import HexBerlekamp.FactorPolyElab
public import HexBerlekamp.FactorPolyElab
public meta import HexBerlekamp.IrreducibilityElab
public import HexBerlekamp.IrreducibilityElab
public meta import HexBerlekampZassenhaus.FactorTactic
public import HexBerlekampZassenhaus.FactorTactic

public section

/-!
Stable user API for executable integer Berlekamp-Zassenhaus factorization.

This umbrella contains the factorization operations and result types, the
integer irreducibility certificates, and the `factor_poly` and
`irreducibility` tactics. Import `HexBerlekampZassenhaus.All` only when
developing the factorization algorithms themselves.
-/
