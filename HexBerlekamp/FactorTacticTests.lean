/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

-- PLAIN `public import` only: NO `import all` (except the `public meta import`
-- required for elaboration-time evaluation of same-library functions). The
-- emitted kernel checks must reduce through the exposed closure alone, exactly
-- as a downstream `module` consumer of the tactics would see them.
public meta import HexBerlekamp.IrreducibilityElab
public import HexBerlekamp.IrreducibilityElab

public section

open Hex

namespace HexBerlekamp.FactorTacticTests

instance : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
instance : ZMod64.Bounds 2 := ⟨by decide, by decide⟩

def z (n : Nat) : ZMod64 5 := ZMod64.ofNat 5 n

/-- `3 · (x+1)² · (x²+2)` over `F_5`: non-monic, non-square-free. -/
def testF : FpPoly 5 :=
  DensePoly.C (z 3) *
    (FpPoly.ofCoeffs #[z 1, z 1] * FpPoly.ofCoeffs #[z 1, z 1] *
     FpPoly.ofCoeffs #[z 2, z 0, z 1])

/-! ## `factor_poly`, term form -/

noncomputable def fac := factor_poly testF

example : fac.factors.length = 3 := rfl
example : fac.scalar = z 3 := rfl

example : True := by
  obtain ⟨scalar, factors, factors_mul, factors_irred⟩ := factor_poly testF
  trivial

-- Edge cases: zero, constants, and units all produce empty factor lists.
noncomputable def facZero := factor_poly (0 : FpPoly 5)
noncomputable def facConst := factor_poly (FpPoly.C (z 4))
example : facZero.factors = [] := rfl
example : facConst.factors = [] := rfl

-- Characteristic-2 inseparable input: (x+1)^4 = x^4+1 over F_2.
def w (n : Nat) : ZMod64 2 := ZMod64.ofNat 2 n
def inseparable : FpPoly 2 := FpPoly.ofCoeffs #[w 1, w 0, w 0, w 0, w 1]
noncomputable def facInsep := factor_poly inseparable
example : facInsep.factors.length = 4 := rfl

-- Raw Berlekamp leaves are only defined up to a unit scalar: over F_3,
-- x⁴ + x³ + x produces non-monic gcd leaves, which `fpFactorSearch` must
-- normalize into monic associates (folding the scalars into the unit).
instance : ZMod64.Bounds 3 := ⟨by decide, by decide⟩
def y (n : Nat) : ZMod64 3 := ZMod64.ofNat 3 n
def rawLeaves : FpPoly 3 := FpPoly.ofCoeffs #[y 0, y 1, y 0, y 1, y 1]
noncomputable def facRawLeaves := factor_poly rawLeaves
example : facRawLeaves.factors.length = 3 := rfl
example : facRawLeaves.scalar = y 1 := rfl

/-! ## `factor_poly`, tactic form -/

example : True := by
  factor_poly testF
  -- `scalar`/`factors` are transparent `let`s; the hypotheses are usable.
  have : factors.length = 3 := rfl
  exact True.intro

/-! ## `irreducibility` -/

def irr1 : FpPoly 5 := FpPoly.ofCoeffs #[z 2, z 0, z 1]
/-- Non-monic irreducible: `3 · (x²+2)`. -/
def irr2 : FpPoly 5 := DensePoly.C (z 3) * irr1

theorem irr1_irred : FpPoly.Irreducible irr1 := irreducibility irr1
theorem irr2_irred : FpPoly.Irreducible irr2 := irreducibility irr2

example : FpPoly.Irreducible irr1 := by irreducibility

example : True := by
  irreducibility irr1
  irreducibility h : irr2
  exact h.elim fun _ _ => True.intro

/-! ## Negative tests -/

instance : ZMod64.Bounds 6 := ⟨by decide, by decide⟩

/-- error: irreducibility: the modulus 6 is not prime; irreducibility over Z/6 needs a prime field -/
#guard_msgs in
example := irreducibility (FpPoly.ofCoeffs #[ZMod64.ofNat 6 1, ZMod64.ofNat 6 1])

/-- error: irreducibility: the zero polynomial is not irreducible -/
#guard_msgs in
example := irreducibility (0 : FpPoly 5)

/--
error: irreducibility: the polynomial
  FpPoly.C (z 4)
is a nonzero constant, hence a unit over F_5, not irreducible
-/
#guard_msgs in
example := irreducibility (FpPoly.C (z 4))

/--
error: irreducibility: the polynomial
  testF
is not irreducible over F_5: factor_poly finds 3 irreducible factors (with multiplicity)
-/
#guard_msgs in
example := irreducibility testF

/-! ## Axiom hygiene -/

/-- info: 'HexBerlekamp.FactorTacticTests.fac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fac

/-- info: 'HexBerlekamp.FactorTacticTests.irr1_irred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms irr1_irred

end HexBerlekamp.FactorTacticTests
