import HexBerlekampZassenhausMathlib.Basic

/-!
Core conformance checks for `hex-berlekamp-zassenhaus-mathlib`.

Oracle: none
Mode: always
Covered operations:
- `irreducibleByFactorization` on transported `Polynomial ℤ` inputs
- `irreducibleDecidablePred` as the Mathlib-facing decidability bridge
- `Hex.factor` observed through `HexPolyZMathlib.ofPolynomial` and
  `HexPolyZMathlib.toPolynomial`
Covered properties:
- executable irreducibility accepts a prime constant and rejects zero and unit
  inputs
- the decidability bridge elaborates for concrete `Polynomial ℤ` inputs
- transporting between `Polynomial ℤ` and `Hex.ZPoly` agrees on the
  nonconstant fixtures used by the executable checks
- executable factor products multiply back to the committed nonconstant inputs
Covered edge cases:
- zero and unit polynomials
- degree-zero prime constants
- primitive linear polynomials
- reducible products of linears
- a small irreducible quadratic over `ℤ`
-/

namespace HexBerlekampZassenhausMathlib

open Polynomial

noncomputable section

private def zpoly (coeffs : Array Int) : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs coeffs

private def linear (r : Int) : Hex.ZPoly :=
  zpoly #[-r, 1]

private def hexZero : Hex.ZPoly := 0

private def hexOne : Hex.ZPoly := 1

private def hexConstantPrime : Hex.ZPoly :=
  zpoly #[5]

private def hexLinearPrimitive : Hex.ZPoly :=
  zpoly #[3, 1]

private def hexReducibleQuadratic : Hex.ZPoly :=
  zpoly #[2, 3, 1]

private def hexIrreducibleQuadratic : Hex.ZPoly :=
  zpoly #[1, 0, 1]

private def mathZero : Polynomial ℤ :=
  HexPolyZMathlib.toPolynomial hexZero

private def mathOne : Polynomial ℤ :=
  HexPolyZMathlib.toPolynomial hexOne

private def mathConstantPrime : Polynomial ℤ :=
  HexPolyZMathlib.toPolynomial hexConstantPrime

private def mathLinearPrimitive : Polynomial ℤ :=
  HexPolyZMathlib.toPolynomial hexLinearPrimitive

private def mathReducibleQuadratic : Polynomial ℤ :=
  HexPolyZMathlib.toPolynomial hexReducibleQuadratic

private def mathIrreducibleQuadratic : Polynomial ℤ :=
  HexPolyZMathlib.toPolynomial hexIrreducibleQuadratic

/-- Executable product guard for the `Factorization` returned by `Hex.factor`. -/
private def factorProductPreserved (f : Hex.ZPoly) : Bool :=
  Hex.Factorization.product (Hex.factor f) == f

/-! ## Irreducibility checks through the transported Mathlib surface -/

example : irreducibleByFactorization mathZero = false := by
  rw [mathZero, irreducibleByFactorization, HexPolyZMathlib.ofPolynomial_toPolynomial]
  rfl

example : irreducibleByFactorization mathOne = false := by
  rw [mathOne, irreducibleByFactorization, HexPolyZMathlib.ofPolynomial_toPolynomial]
  rfl

example : irreducibleByFactorization mathConstantPrime = true := by
  rw [mathConstantPrime, irreducibleByFactorization, HexPolyZMathlib.ofPolynomial_toPolynomial]
  rfl

/-! ## Decidability elaboration for representative `Polynomial ℤ` inputs -/

example : Decidable (Irreducible mathZero) := inferInstance

example : Decidable (Irreducible mathOne) := inferInstance

example : Decidable (Irreducible mathConstantPrime) := inferInstance

example : Decidable (Irreducible mathLinearPrimitive) := inferInstance

example : Decidable (Irreducible mathReducibleQuadratic) := inferInstance

example : Decidable (Irreducible mathIrreducibleQuadratic) := inferInstance

/-! ## Round-trip checks for the conversion boundary -/

example :
    HexPolyZMathlib.toPolynomial (HexPolyZMathlib.ofPolynomial mathLinearPrimitive) =
      mathLinearPrimitive :=
  HexPolyZMathlib.toPolynomial_ofPolynomial mathLinearPrimitive

example :
    HexPolyZMathlib.toPolynomial (HexPolyZMathlib.ofPolynomial mathReducibleQuadratic) =
      mathReducibleQuadratic :=
  HexPolyZMathlib.toPolynomial_ofPolynomial mathReducibleQuadratic

example :
    HexPolyZMathlib.toPolynomial (HexPolyZMathlib.ofPolynomial mathIrreducibleQuadratic) =
      mathIrreducibleQuadratic :=
  HexPolyZMathlib.toPolynomial_ofPolynomial mathIrreducibleQuadratic

example :
    HexPolyZMathlib.ofPolynomial (HexPolyZMathlib.toPolynomial (linear (-3))) =
      linear (-3) :=
  HexPolyZMathlib.ofPolynomial_toPolynomial (linear (-3))

example :
    HexPolyZMathlib.ofPolynomial (HexPolyZMathlib.toPolynomial (zpoly #[2, 3, 1])) =
      zpoly #[2, 3, 1] :=
  HexPolyZMathlib.ofPolynomial_toPolynomial (zpoly #[2, 3, 1])

/-! ## Product preservation guards for the public `Factorization` convention -/

#guard factorProductPreserved hexZero

#guard factorProductPreserved hexOne

#guard factorProductPreserved hexConstantPrime

#guard factorProductPreserved hexLinearPrimitive

#guard factorProductPreserved hexReducibleQuadratic

#guard factorProductPreserved hexIrreducibleQuadratic

end

end HexBerlekampZassenhausMathlib
