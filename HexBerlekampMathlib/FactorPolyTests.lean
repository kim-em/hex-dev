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
public meta import HexBerlekampMathlib.FactorProvider
public import HexBerlekamp.IrreducibilityElab
public import HexBerlekampMathlib.FactorProvider

public section

open Polynomial

namespace HexBerlekampMathlib.FactorPolyTests

/-! ## `factor_poly` on `Polynomial (ZMod 5)` -/

/-- `3·(x+1)²·(x²+2)` over `F_5`: non-monic, non-square-free. -/
noncomputable def facP :=
  factor_poly ((X + 1) * (X + 1) * (X ^ 2 + 2) * 3 : Polynomial (ZMod 5))

example : facP.factors.length = 3 := rfl

example : True := by
  obtain ⟨scalar, factors, factors_mul, factors_irred⟩ :=
    factor_poly ((X + 1) * (X + 1) * (X ^ 2 + 2) * 3 : Polynomial (ZMod 5))
  trivial

-- Tactic form: providers emitting `FactoredPoly.ofFp` land as a single
-- `factored` hypothesis.
example : True := by
  factor_poly ((X + 1) * (X + 1) * (X ^ 2 + 2) * 3 : Polynomial (ZMod 5))
  exact True.intro

-- Negation and subtraction arms; `Polynomial.C` coefficients.
noncomputable def facNeg :=
  factor_poly (-(X + 1) * (X - 1) * Polynomial.C 2 : Polynomial (ZMod 5))

/-! ## `irreducibility` on `Polynomial (ZMod 5)` -/

theorem quad_irred : Irreducible (X ^ 2 + 2 : Polynomial (ZMod 5)) :=
  irreducibility (X ^ 2 + 2 : Polynomial (ZMod 5))

-- Coefficient over the modulus (7 ≡ 2 mod 5) and a negative coefficient
-- (X² - 3 = X² + 2 mod 5).
theorem quad_irred_big : Irreducible (X ^ 2 + 7 : Polynomial (ZMod 5)) :=
  irreducibility (X ^ 2 + 7 : Polynomial (ZMod 5))

theorem quad_irred_negc : Irreducible (X ^ 2 - 3 : Polynomial (ZMod 5)) :=
  irreducibility (X ^ 2 - 3 : Polynomial (ZMod 5))

-- Goal form.
example : Irreducible (X ^ 2 + 2 : Polynomial (ZMod 5)) := by irreducibility

-- `h :` and `this` tactic forms.
example : True := by
  irreducibility (X ^ 2 + 2 : Polynomial (ZMod 5))
  irreducibility h : (Polynomial.C 3 * X + 1 : Polynomial (ZMod 5))
  exact True.intro

/-! ## Reducible/degenerate inputs: targeted errors -/

/--
error: irreducibility: the polynomial
  X ^ 2 + 4
is not irreducible over F_5: factor_poly finds 2 irreducible factors (with multiplicity)
-/
#guard_msgs in
example := irreducibility (X ^ 2 + 4 : Polynomial (ZMod 5))

/-- error: irreducibility: the zero polynomial is not irreducible -/
#guard_msgs in
example := irreducibility (0 : Polynomial (ZMod 5))

/--
error: irreducibility: the polynomial
  3
is a nonzero constant, hence a unit over F_5, not irreducible
-/
#guard_msgs in
example := irreducibility (3 : Polynomial (ZMod 5))

/-! ## Composite modulus: the provider declines, the driver reports -/

/--
info: factor_poly: unsupported polynomial type
  (ZMod 6)[X]
Supported without further imports: Hex.FpPoly p (prime p). Importing HexBerlekampZassenhaus adds Hex.ZPoly; the Mathlib bridge libraries add Polynomial (ZMod q) and Polynomial ℤ.

factor_poly: Polynomial (ZMod q) inputs need a prime modulus, but 6 is not prime
-/
#guard_msgs in
#check_failure (factor_poly (X + 1 : Polynomial (ZMod 6)))

/--
info: irreducibility: unsupported polynomial type
  (ZMod 6)[X]
Supported without further imports: Hex.FpPoly p (prime p). Importing HexBerlekampZassenhaus adds Hex.ZPoly; the Mathlib bridge libraries add Polynomial (ZMod q) and Polynomial ℤ.

irreducibility: Polynomial (ZMod q) inputs need a prime modulus, but 6 is not prime
-/
#guard_msgs in
#check_failure (irreducibility (X + 1 : Polynomial (ZMod 6)))

/-! ## Axiom hygiene -/

/-- info: 'HexBerlekampMathlib.FactorPolyTests.facP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms facP

/-- info: 'HexBerlekampMathlib.FactorPolyTests.facNeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms facNeg

/-- info: 'HexBerlekampMathlib.FactorPolyTests.quad_irred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quad_irred

end HexBerlekampMathlib.FactorPolyTests
