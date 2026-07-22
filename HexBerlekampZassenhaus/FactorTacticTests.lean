/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

-- PLAIN `public import` only (plus the `public meta import` required for
-- elaboration-time evaluation): the emitted kernel checks must reduce through
-- the exposed closure alone.
public meta import HexBerlekamp.IrreducibilityElab
public meta import HexBerlekampZassenhaus.FactorProvider
public import HexBerlekamp.IrreducibilityElab
public import HexBerlekampZassenhaus.FactorProvider

public section

open Hex

namespace HexBerlekampZassenhaus.FactorTacticTests

/-- `-6·(x+1)²·(x²+1)`: content, sign, and multiplicity. -/
def testZ : ZPoly :=
  DensePoly.C (-6) * (DensePoly.ofCoeffs #[1, 1] * DensePoly.ofCoeffs #[1, 1] *
    DensePoly.ofCoeffs #[1, 0, 1])

noncomputable def facZ := factor_poly testZ

example : facZ.scalar = -6 := rfl
example : facZ.factors.length = 3 := rfl

example : True := by
  obtain ⟨scalar, factors, factors_mul, factors_irred⟩ := factor_poly testZ
  trivial

example : True := by
  factor_poly testZ
  have : scalar = -6 := rfl
  exact True.intro

/-! ## `irreducibility` on ZPoly -/

def linZ : ZPoly := DensePoly.ofCoeffs #[3, 2]
def quadZ : ZPoly := DensePoly.ofCoeffs #[1, 0, 1]
def constZ : ZPoly := DensePoly.C (-7)

theorem lin_irred : ZPoly.Irreducible linZ := irreducibility linZ
theorem quad_irred : ZPoly.Irreducible quadZ := irreducibility quadZ
theorem const_irred : ZPoly.Irreducible constZ := irreducibility constZ

example : ZPoly.Irreducible quadZ := by irreducibility

example : True := by
  irreducibility h : linZ
  exact True.intro

/-! ## Balanced inputs: no free-layer certificate, clean decline -/

/-- `X⁴+1`: irreducible over ℤ but reducible mod every prime — no
single-prime witness exists, so the free layer declines (the Mathlib bridge
provider handles it via Eisenstein-after-shift / multi-prime certificates
when imported). -/
def x4p1 : ZPoly := DensePoly.ofCoeffs #[1, 0, 0, 0, 1]

#check_failure (irreducibility x4p1)

/-- A product with a Swinnerton-Dyer factor: `(x+1)·(x⁴−10x²+1)`. The
factorization search succeeds but the SD factor has no free-layer witness,
so `factor_poly` declines. -/
def sdProd : ZPoly :=
  DensePoly.ofCoeffs #[1, 1] * DensePoly.ofCoeffs #[1, 0, -10, 0, 1]

#check_failure (factor_poly sdProd)

/-! ## Reducible/unit inputs: targeted errors -/

/--
info: irreducibility: the polynomial
  testZ
is not irreducible over ℤ: factor_poly finds 3 irreducible factors (with multiplicity), scalar -6
-/
#guard_msgs in
#check_failure (irreducibility testZ)

/-- info: irreducibility: the polynomial
  DensePoly.C 1
is a unit (±1), not irreducible -/
#guard_msgs in
#check_failure (irreducibility (DensePoly.C (1 : Int)))

/-! ## Axiom hygiene -/

/-- info: 'HexBerlekampZassenhaus.FactorTacticTests.facZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms facZ

/-- info: 'HexBerlekampZassenhaus.FactorTacticTests.quad_irred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quad_irred

end HexBerlekampZassenhaus.FactorTacticTests
