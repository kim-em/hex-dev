import HexPolyMathlib.Euclid

/-!
Core conformance checks for `hex-poly-mathlib`.

Oracle: none
Mode: always
Covered operations:
- `toPolynomial` and `ofPolynomial` conversion functions
- `equiv` and `equiv.symm` ring-equivalence bridge functions
- gcd and xgcd correspondence surfaces (`toPolynomial_gcd_associated`,
  `equiv_gcd_associated`, `toPolynomial_xgcd_left`, `toPolynomial_xgcd_right`,
  `toPolynomial_xgcd_gcd_associated`,
  `toPolynomial_xgcd_bezout`)
Covered properties:
- converting executable dense polynomials to Mathlib polynomials and back preserves
  committed normalized inputs
- converting Mathlib polynomials to executable dense polynomials and back preserves
  committed polynomial inputs
- `equiv` and `equiv.symm` agree with the concrete conversion functions on committed inputs
- executable raw gcd/xgcd gcd results transport to associated polynomials against
  Mathlib's normalized Euclidean-domain gcd on committed `Rat` inputs
- executable xgcd coefficients transport to Mathlib's Bezout coefficient surfaces on
  committed `Rat` inputs
- transported xgcd coefficients satisfy the Bezout identity against Mathlib gcd
Covered edge cases:
- zero polynomials
- degree-zero constant polynomials
- normalized sparse inputs with internal zero coefficients
- raw trailing-zero dense inputs
- exact gcd pairs and zero-left gcd pairs over `Rat`
-/

namespace HexPolyMathlib

noncomputable section

private def denseTypical : Hex.DensePoly Rat :=
  Hex.DensePoly.ofCoeffs #[3, 0, -2]

private def denseZero : Hex.DensePoly Rat :=
  0

private def denseTrailingZeros : Hex.DensePoly Rat :=
  Hex.DensePoly.ofCoeffs #[0, 4, 0, -5, 0, 0]

private def mathTypical : Polynomial Rat :=
  Polynomial.C 3 - Polynomial.C 2 * Polynomial.X ^ 2

private def mathZero : Polynomial Rat :=
  0

private def mathTrailingZeros : Polynomial Rat :=
  Polynomial.C 4 * Polynomial.X - Polynomial.C 5 * Polynomial.X ^ 3

private def mathConstant : Polynomial Rat :=
  Polynomial.C (-7)

private def gcdTypicalLeft : Hex.DensePoly Rat :=
  Hex.DensePoly.ofCoeffs #[-2, 1, 1]

private def gcdTypicalRight : Hex.DensePoly Rat :=
  Hex.DensePoly.ofCoeffs #[-3, 2, 1]

private def gcdZeroLeft : Hex.DensePoly Rat :=
  0

private def gcdZeroRight : Hex.DensePoly Rat :=
  Hex.DensePoly.ofCoeffs #[2, 1]

private def gcdAdversarialLeft : Hex.DensePoly Rat :=
  Hex.DensePoly.ofCoeffs #[2, 5, 2]

private def gcdAdversarialRight : Hex.DensePoly Rat :=
  Hex.DensePoly.ofCoeffs #[1, 2]

example : toPolynomial (ofPolynomial mathTypical) = mathTypical :=
  toPolynomial_ofPolynomial mathTypical

example : toPolynomial (ofPolynomial mathZero) = mathZero :=
  toPolynomial_ofPolynomial mathZero

example : toPolynomial (ofPolynomial mathTrailingZeros) = mathTrailingZeros :=
  toPolynomial_ofPolynomial mathTrailingZeros

example : toPolynomial (ofPolynomial mathConstant) = mathConstant :=
  toPolynomial_ofPolynomial mathConstant

example : ofPolynomial (toPolynomial denseTypical) = denseTypical :=
  ofPolynomial_toPolynomial denseTypical

example : ofPolynomial (toPolynomial denseZero) = denseZero :=
  ofPolynomial_toPolynomial denseZero

example : ofPolynomial (toPolynomial denseTrailingZeros) = denseTrailingZeros :=
  ofPolynomial_toPolynomial denseTrailingZeros

example : equiv denseTypical = toPolynomial denseTypical :=
  equiv_apply denseTypical

example : equiv denseZero = toPolynomial denseZero :=
  equiv_apply denseZero

example : equiv denseTrailingZeros = toPolynomial denseTrailingZeros :=
  equiv_apply denseTrailingZeros

example : equiv.symm mathTypical = ofPolynomial mathTypical :=
  equiv_symm_apply mathTypical

example : equiv.symm mathZero = ofPolynomial mathZero :=
  equiv_symm_apply mathZero

example : equiv.symm mathTrailingZeros = ofPolynomial mathTrailingZeros :=
  equiv_symm_apply mathTrailingZeros

variable [Hex.DensePoly.GcdLaws Rat]

example :
    Associated (toPolynomial (Hex.DensePoly.gcd gcdTypicalLeft gcdTypicalRight))
      (EuclideanDomain.gcd (toPolynomial gcdTypicalLeft) (toPolynomial gcdTypicalRight)) :=
  toPolynomial_gcd_associated gcdTypicalLeft gcdTypicalRight

example :
    Associated (toPolynomial (Hex.DensePoly.gcd gcdZeroLeft gcdZeroRight))
      (EuclideanDomain.gcd (toPolynomial gcdZeroLeft) (toPolynomial gcdZeroRight)) :=
  toPolynomial_gcd_associated gcdZeroLeft gcdZeroRight

example :
    Associated (toPolynomial (Hex.DensePoly.gcd gcdAdversarialLeft gcdAdversarialRight))
      (EuclideanDomain.gcd (toPolynomial gcdAdversarialLeft) (toPolynomial gcdAdversarialRight)) :=
  toPolynomial_gcd_associated gcdAdversarialLeft gcdAdversarialRight

example :
    toPolynomial (Hex.DensePoly.xgcd gcdTypicalLeft gcdTypicalRight).left =
      EuclideanDomain.gcdA (toPolynomial gcdTypicalLeft) (toPolynomial gcdTypicalRight) :=
  toPolynomial_xgcd_left gcdTypicalLeft gcdTypicalRight

example :
    toPolynomial (Hex.DensePoly.xgcd gcdZeroLeft gcdZeroRight).left =
      EuclideanDomain.gcdA (toPolynomial gcdZeroLeft) (toPolynomial gcdZeroRight) :=
  toPolynomial_xgcd_left gcdZeroLeft gcdZeroRight

example :
    toPolynomial (Hex.DensePoly.xgcd gcdAdversarialLeft gcdAdversarialRight).left =
      EuclideanDomain.gcdA (toPolynomial gcdAdversarialLeft) (toPolynomial gcdAdversarialRight) :=
  toPolynomial_xgcd_left gcdAdversarialLeft gcdAdversarialRight

example :
    toPolynomial (Hex.DensePoly.xgcd gcdTypicalLeft gcdTypicalRight).right =
      EuclideanDomain.gcdB (toPolynomial gcdTypicalLeft) (toPolynomial gcdTypicalRight) :=
  toPolynomial_xgcd_right gcdTypicalLeft gcdTypicalRight

example :
    toPolynomial (Hex.DensePoly.xgcd gcdZeroLeft gcdZeroRight).right =
      EuclideanDomain.gcdB (toPolynomial gcdZeroLeft) (toPolynomial gcdZeroRight) :=
  toPolynomial_xgcd_right gcdZeroLeft gcdZeroRight

example :
    toPolynomial (Hex.DensePoly.xgcd gcdAdversarialLeft gcdAdversarialRight).right =
      EuclideanDomain.gcdB (toPolynomial gcdAdversarialLeft) (toPolynomial gcdAdversarialRight) :=
  toPolynomial_xgcd_right gcdAdversarialLeft gcdAdversarialRight

example :
    Associated (toPolynomial (Hex.DensePoly.xgcd gcdTypicalLeft gcdTypicalRight).gcd)
      (EuclideanDomain.gcd (toPolynomial gcdTypicalLeft) (toPolynomial gcdTypicalRight)) :=
  toPolynomial_xgcd_gcd_associated gcdTypicalLeft gcdTypicalRight

example :
    Associated (toPolynomial (Hex.DensePoly.xgcd gcdZeroLeft gcdZeroRight).gcd)
      (EuclideanDomain.gcd (toPolynomial gcdZeroLeft) (toPolynomial gcdZeroRight)) :=
  toPolynomial_xgcd_gcd_associated gcdZeroLeft gcdZeroRight

example :
    Associated (toPolynomial (Hex.DensePoly.xgcd gcdAdversarialLeft gcdAdversarialRight).gcd)
      (EuclideanDomain.gcd (toPolynomial gcdAdversarialLeft) (toPolynomial gcdAdversarialRight)) :=
  toPolynomial_xgcd_gcd_associated gcdAdversarialLeft gcdAdversarialRight

example :
    toPolynomial (Hex.DensePoly.xgcd gcdTypicalLeft gcdTypicalRight).left *
        toPolynomial gcdTypicalLeft +
      toPolynomial (Hex.DensePoly.xgcd gcdTypicalLeft gcdTypicalRight).right *
        toPolynomial gcdTypicalRight =
      EuclideanDomain.gcd (toPolynomial gcdTypicalLeft) (toPolynomial gcdTypicalRight) :=
  toPolynomial_xgcd_bezout gcdTypicalLeft gcdTypicalRight

example :
    toPolynomial (Hex.DensePoly.xgcd gcdZeroLeft gcdZeroRight).left *
        toPolynomial gcdZeroLeft +
      toPolynomial (Hex.DensePoly.xgcd gcdZeroLeft gcdZeroRight).right *
        toPolynomial gcdZeroRight =
      EuclideanDomain.gcd (toPolynomial gcdZeroLeft) (toPolynomial gcdZeroRight) :=
  toPolynomial_xgcd_bezout gcdZeroLeft gcdZeroRight

example :
    toPolynomial (Hex.DensePoly.xgcd gcdAdversarialLeft gcdAdversarialRight).left *
        toPolynomial gcdAdversarialLeft +
      toPolynomial (Hex.DensePoly.xgcd gcdAdversarialLeft gcdAdversarialRight).right *
        toPolynomial gcdAdversarialRight =
      EuclideanDomain.gcd (toPolynomial gcdAdversarialLeft) (toPolynomial gcdAdversarialRight) :=
  toPolynomial_xgcd_bezout gcdAdversarialLeft gcdAdversarialRight

example :
    Associated (equiv (Hex.DensePoly.gcd gcdTypicalLeft gcdTypicalRight))
      (EuclideanDomain.gcd (equiv gcdTypicalLeft) (equiv gcdTypicalRight)) :=
  equiv_gcd_associated gcdTypicalLeft gcdTypicalRight

example :
    Associated (equiv (Hex.DensePoly.gcd gcdZeroLeft gcdZeroRight))
      (EuclideanDomain.gcd (equiv gcdZeroLeft) (equiv gcdZeroRight)) :=
  equiv_gcd_associated gcdZeroLeft gcdZeroRight

example :
    Associated (equiv (Hex.DensePoly.gcd gcdAdversarialLeft gcdAdversarialRight))
      (EuclideanDomain.gcd (equiv gcdAdversarialLeft) (equiv gcdAdversarialRight)) :=
  equiv_gcd_associated gcdAdversarialLeft gcdAdversarialRight

end

end HexPolyMathlib
