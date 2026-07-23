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

/-! ## Eisenstein-after-shift certificates -/

/-- `X⁴+1`: irreducible over ℤ but reducible mod every prime, so there is no
single-prime witness; the Eisenstein-after-shift search certifies it at
shift `1`, prime `2` (`(X+1)⁴+1 = X⁴+4X³+6X²+4X+2`). -/
def x4p1 : ZPoly := DensePoly.ofCoeffs #[1, 0, 0, 0, 1]

theorem x4p1_irred : ZPoly.Irreducible x4p1 := irreducibility x4p1

/-- `X²-2`: plain Eisenstein at prime `2`, shift `0`. The tactic itself
certifies this via the mod-3 route, so the shift-`0` Eisenstein witness is
exercised directly through the checker and its soundness theorem. -/
def x2m2 : ZPoly := DensePoly.ofCoeffs #[-2, 0, 1]

example : ZPoly.checkIrredWitness x2m2 (.eisenstein 2 0) = true := rfl

theorem x2m2_irred : ZPoly.Irreducible x2m2 :=
  ZPoly.irreducible_of_checkIrredWitness x2m2 (.eisenstein 2 0) rfl

/-- The largest admissible Eisenstein prime (`eisensteinPrimeCap = 128`, so
prime `127`) still kernel-replays within the default `maxRecDepth`: the
`isPrimeTrial` reduction is depth-linear in the prime, and stalls a little
above 150, which is why the search caps its candidates. -/
def x2m127 : ZPoly := DensePoly.ofCoeffs #[-127, 0, 1]

example : ZPoly.checkIrredWitness x2m127 (.eisenstein 127 0) = true := rfl

/-! ## Balanced inputs: no free-layer certificate, clean decline -/

/-- A product with a Swinnerton-Dyer factor: `(x+1)·(x⁴−10x²+1)`. The
factorization search succeeds but the SD factor has no free-layer witness
(it is reducible mod every prime and not Eisenstein at any small shift), so
`factor_poly` declines. -/
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

/--
info: irreducibility: deciding primality of the constant
  DensePoly.C 67108879
needs a kernel replay of roughly 67108879 steps, over the supported budget (67108864)
-/
#guard_msgs in
#check_failure (irreducibility (DensePoly.C (67108879 : Int)))

/-! ## Axiom hygiene -/

/-- info: 'HexBerlekampZassenhaus.FactorTacticTests.facZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms facZ

/-- info: 'HexBerlekampZassenhaus.FactorTacticTests.quad_irred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quad_irred

/-- info: 'HexBerlekampZassenhaus.FactorTacticTests.x4p1_irred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms x4p1_irred

/-- info: 'HexBerlekampZassenhaus.FactorTacticTests.x2m2_irred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms x2m2_irred

end HexBerlekampZassenhaus.FactorTacticTests
