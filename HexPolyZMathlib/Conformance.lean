import HexPolyZMathlib.Basic

/-!
Core conformance checks for `hex-poly-z-mathlib`.

Oracle: none
Mode: always
Covered operations:
- `toPolynomial` — `Hex.ZPoly` to `Polynomial ℤ` conversion
- `ofPolynomial` — `Polynomial ℤ` to `Hex.ZPoly` conversion
- `equiv` — ring equivalence application
- `equiv.symm` — ring equivalence inverse application
- simp-bridge lemmas: `coeff_toPolynomial`, `toPolynomial_zero`,
  `toPolynomial_C`, `toPolynomial_add`, `toPolynomial_mul`,
  `toPolynomial_ofPolynomial`, `ofPolynomial_toPolynomial`,
  `equiv_apply`, `equiv_symm_apply`
Covered properties:
- `Polynomial ℤ → Hex.ZPoly → Polynomial ℤ` round trip recovers the
  Mathlib polynomial.
- `Hex.ZPoly → Polynomial ℤ → Hex.ZPoly` round trip recovers the
  executable polynomial.
- `equiv` and `equiv.symm` agree pointwise with the named conversion
  functions.
- `toPolynomial` preserves zero, scalars (`C`), addition, and
  multiplication.
- `coeff_toPolynomial` exposes the executable polynomial's coefficient
  function through the bridge.
Covered edge cases:
- the zero `Hex.ZPoly` and the zero `Polynomial ℤ`.
- a degree-zero constant integer polynomial.
- raw dense input with internal and trailing zero coefficients.
- a typical mid-size integer polynomial with mixed signs (degree 9).
- multiplication factors whose product reaches the upper end of the
  `core` profile size band (degree 8).
-/

namespace HexPolyZMathlib

noncomputable section

private def denseTypical : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs #[3, 0, -2, 5, 1, -4, 0, 7, -6, 2]

private def denseZero : Hex.ZPoly := 0

private def denseTrailingZeros : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs #[0, 4, 0, -5, 0, 7, 0, 0, 0]

private def denseConstant : Hex.ZPoly :=
  Hex.DensePoly.C (-7 : ℤ)

private def denseAddendA : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs #[1, -2, 3, 0, 4, -1, 2]

private def denseAddendB : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs #[0, 5, -3, 2, 1, 0, 1, -4]

private def denseFactorA : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs #[2, 1, -1, 3, 1]

private def denseFactorB : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs #[1, 0, 3, -2, 1]

private def mathTypical : Polynomial ℤ :=
  Polynomial.C 3 - Polynomial.C 2 * Polynomial.X ^ 2
    + Polynomial.C 5 * Polynomial.X ^ 3 + Polynomial.X ^ 4
    - Polynomial.C 4 * Polynomial.X ^ 5 + Polynomial.C 7 * Polynomial.X ^ 7
    - Polynomial.C 6 * Polynomial.X ^ 8 + Polynomial.C 2 * Polynomial.X ^ 9

private def mathZero : Polynomial ℤ := 0

private def mathTrailingZeros : Polynomial ℤ :=
  Polynomial.C 4 * Polynomial.X - Polynomial.C 5 * Polynomial.X ^ 3
    + Polynomial.C 7 * Polynomial.X ^ 5

private def mathConstant : Polynomial ℤ :=
  Polynomial.C (-7)

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

example : ofPolynomial (toPolynomial denseConstant) = denseConstant :=
  ofPolynomial_toPolynomial denseConstant

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

example : toPolynomial (0 : Hex.ZPoly) = (0 : Polynomial ℤ) :=
  toPolynomial_zero

example : toPolynomial (Hex.DensePoly.C (3 : ℤ)) = Polynomial.C 3 :=
  toPolynomial_C 3

example : toPolynomial (Hex.DensePoly.C (-7 : ℤ)) = Polynomial.C (-7) :=
  toPolynomial_C (-7)

example : toPolynomial (Hex.DensePoly.C (0 : ℤ)) = Polynomial.C 0 :=
  toPolynomial_C 0

example :
    toPolynomial (denseAddendA + denseAddendB) =
      toPolynomial denseAddendA + toPolynomial denseAddendB :=
  toPolynomial_add denseAddendA denseAddendB

example :
    toPolynomial (denseAddendA + 0) =
      toPolynomial denseAddendA + toPolynomial 0 :=
  toPolynomial_add denseAddendA 0

example :
    toPolynomial (denseTrailingZeros + denseAddendA) =
      toPolynomial denseTrailingZeros + toPolynomial denseAddendA :=
  toPolynomial_add denseTrailingZeros denseAddendA

example :
    toPolynomial (denseFactorA * denseFactorB) =
      toPolynomial denseFactorA * toPolynomial denseFactorB :=
  toPolynomial_mul denseFactorA denseFactorB

example :
    toPolynomial (denseFactorA * 0) =
      toPolynomial denseFactorA * toPolynomial 0 :=
  toPolynomial_mul denseFactorA 0

example :
    toPolynomial (denseTrailingZeros * denseFactorA) =
      toPolynomial denseTrailingZeros * toPolynomial denseFactorA :=
  toPolynomial_mul denseTrailingZeros denseFactorA

example (n : Nat) :
    (toPolynomial denseTypical).coeff n = denseTypical.coeff n :=
  coeff_toPolynomial denseTypical n

example (n : Nat) :
    (toPolynomial denseZero).coeff n = denseZero.coeff n :=
  coeff_toPolynomial denseZero n

example (n : Nat) :
    (toPolynomial denseTrailingZeros).coeff n = denseTrailingZeros.coeff n :=
  coeff_toPolynomial denseTrailingZeros n

end

end HexPolyZMathlib
