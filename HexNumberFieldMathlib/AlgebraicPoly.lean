/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Lazy

public section

/-!
# Semantic algebraic-coefficient polynomials

The executable representation stores coefficients in increasing degree order.
Horner interpretation into `Polynomial ℂ` makes semantic trailing-zero
normalization explicit without adding structural equality to algebraic
numbers.
-/

namespace Hex.AlgebraicPoly

/-- Interpret a normalized executable algebraic polynomial in `Polynomial ℂ`. -/
@[expose]
noncomputable def toPolynomial (f : AlgebraicPoly) : Polynomial ℂ :=
  f.coeffs.foldr
    (fun a value => Polynomial.C a.toComplex + Polynomial.X * value) 0

/-- Semantic coefficients agree with the executable coefficient accessor. -/
theorem coeff_toPolynomial (f : AlgebraicPoly) (n : Nat) :
    f.toPolynomial.coeff n = (f.coeff n).toComplex := by
  sorry

/-- Executable semantic-zero detection is exact. -/
theorem isZero_iff (f : AlgebraicPoly) :
    f.isZero ↔ f.toPolynomial = 0 := by
  sorry

/-- A nonzero executable polynomial has the same natural degree as its
semantic interpretation. -/
theorem natDegree_toPolynomial (f : AlgebraicPoly) (h : !f.isZero) :
    f.toPolynomial.natDegree = f.degree?.getD 0 := by
  sorry

end Hex.AlgebraicPoly
