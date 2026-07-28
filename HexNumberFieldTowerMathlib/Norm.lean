/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.Arithmetic
public import HexResultantMathlib

public section

/-!
# Tower polynomial and relative norm semantics

The actual interpretation functions in this module make the one-level
resultant statement precise before the later Trager proof consumes it.
-/

namespace Hex.NumberTower

/-- Interpret a dense tower polynomial through the fixed complex embedding. -/
@[expose]
noncomputable def toPolynomial (T : NumberTower) (f : Poly T) : Polynomial ℂ :=
  f.toArray.foldr
    (fun a value => Polynomial.C (T.toComplex a) + Polynomial.X * value) 0

/-- Semantic tower-polynomial coefficients agree with executable access. -/
theorem coeff_toPolynomial (T : NumberTower) (f : Poly T) (n : Nat) :
    (T.toPolynomial f).coeff n = T.toComplex (f.coeff n) := by
  sorry

namespace Norm

/-- Interpret raw coordinates for a validated level list. The fallback is
unreachable when the list comes from a {name}`Hex.NumberTower`. -/
@[expose]
noncomputable def rawToComplex (levels : List Level) (a : Array Rat) : ℂ :=
  (RawEvaluation.evalCoords? levels a).map AlgebraicRoot.toComplex |>.getD 0

/-- Interpret a raw lower-tower dense polynomial in `Polynomial ℂ`. -/
@[expose]
noncomputable def rawPolynomial (levels : List Level)
    (f : DensePoly (Arithmetic.RawElem levels)) : Polynomial ℂ :=
  f.toArray.foldr
    (fun a value =>
      Polynomial.C (rawToComplex levels a.data) + Polynomial.X * value) 0

/-- Interpret an outer dense polynomial over raw lower-tower polynomials. -/
@[expose]
noncomputable def rawOuter (levels : List Level)
    (f : DensePoly (DensePoly (Arithmetic.RawElem levels))) :
    Polynomial (Polynomial ℂ) :=
  f.toArray.foldr
    (fun a value => Polynomial.C (rawPolynomial levels a) +
      Polynomial.X * value) 0

/-- One executable Trager elimination step is the corresponding polynomial
resultant after semantic interpretation of the lower tower. -/
theorem oneLevel_resultant (level : Level) (lower : List Level)
    (hlower : LevelsValid lower) (f : Array (Array Rat)) (c : Int) :
    rawPolynomial lower
        (DensePoly.ofCoeffs <| (oneLevel level lower f c).map
          (Arithmetic.raw lower)) =
      Polynomial.resultant
        (rawOuter lower (definingOuter level lower))
        (rawOuter lower (shiftedOuter level lower f c))
        (m := (definingOuter level lower).degree?.getD 0)
        (n := (shiftedOuter level lower f c).degree?.getD 0) := by
  sorry

/-- The finite characteristic-zero collision bound finds a squarefree norm
for a squarefree positive-degree component in a validated top level. -/
theorem findSquarefreeShift_isSome (T : NumberTower)
    (level : Level) (lower : List Level)
    (hlevels : T.levels.toList = level :: lower)
    (f : Array (Array Rat))
    (hdegree : 0 < f.size - 1)
    (hsquarefree : Squarefree
      (rawPolynomial (level :: lower)
        (DensePoly.ofCoeffs <| f.map
          (Arithmetic.raw (level :: lower))))) :
    (findSquarefreeShift level lower f).isSome := by
  sorry

end Norm

end Hex.NumberTower
