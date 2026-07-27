/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Basic
public import Mathlib.RingTheory.AdjoinRoot

public section

/-!
# Fixed-presentation semantic laws

These are the operation laws needed to transfer a field structure to
`QAdjoin`.  The executable carrier deliberately supplies only its concrete
operations; the eventual `AdjoinRoot` correspondence will package these laws
without changing those operations or their rational scalar action.
-/

namespace Hex.QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

/-- The monic rational associate used for the quotient-field comparison. -/
@[expose]
noncomputable def definingPolynomial (p : ZPoly) : Polynomial Rat :=
  (p.leadingCoeff : Rat)⁻¹ • HexPolyZMathlib.toPolyℚ p

/-- Send reduced executable coordinates to the corresponding `AdjoinRoot`
class. This function is defined before a ring structure is installed on
`QAdjoin`. -/
@[expose]
noncomputable def toAdjoinRoot (a : QAdjoin p x) :
    AdjoinRoot (definingPolynomial p) :=
  AdjoinRoot.mk (definingPolynomial p)
    (HexPolyMathlib.toPolynomial a.coeffs)

/-- Reduced coordinates give a bijection with the quotient by the monic
rational defining relation. -/
theorem toAdjoinRoot_bijective [ZPoly.CheckedIrreducible p] :
    Function.Bijective (@toAdjoinRoot p x) := by
  sorry

/-- Fixed-presentation zero evaluates to complex zero. -/
theorem map_zero (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    toComplex (0 : QAdjoin p x) rep h = 0 := by
  change
    (HexPolyMathlib.toPolynomial (0 : DensePoly Rat)).eval₂
        (algebraMap Rat ℂ) rep.root = 0
  rw [HexPolyMathlib.toPolynomial_zero, Polynomial.eval₂_zero]

/-- Fixed-presentation one evaluates to complex one. -/
theorem map_one (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    toComplex (1 : QAdjoin p x) rep h = 1 := by
  change
    (HexPolyMathlib.toPolynomial (1 : DensePoly Rat)).eval₂
        (algebraMap Rat ℂ) rep.root = 1
  rw [HexPolyMathlib.toPolynomial_one, Polynomial.eval₂_one]

/-- Fixed-presentation negation agrees with complex negation. -/
theorem map_neg (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    toComplex (-a) rep h = -toComplex a rep h := by
  change
    (HexPolyMathlib.toPolynomial
      (reduceCoeffs p (-a.coeffs))).eval₂
        (algebraMap Rat ℂ) rep.root =
      -(HexPolyMathlib.toPolynomial a.coeffs).eval₂
        (algebraMap Rat ℂ) rep.root
  rw [eval_reduceCoeffs, HexPolyMathlib.toPolynomial_neg,
    Polynomial.eval₂_neg]

/-- Fixed-presentation subtraction agrees with complex subtraction. -/
theorem map_sub (a b : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    toComplex (a - b) rep h = toComplex a rep h - toComplex b rep h := by
  change
    (HexPolyMathlib.toPolynomial
      (reduceCoeffs p (a.coeffs - b.coeffs))).eval₂
        (algebraMap Rat ℂ) rep.root =
      (HexPolyMathlib.toPolynomial a.coeffs).eval₂
          (algebraMap Rat ℂ) rep.root -
        (HexPolyMathlib.toPolynomial b.coeffs).eval₂
          (algebraMap Rat ℂ) rep.root
  rw [eval_reduceCoeffs, HexPolyMathlib.toPolynomial_sub,
    Polynomial.eval₂_sub]

/-- The executable rational scalar action is semantic scalar multiplication. -/
theorem map_smul (q : Rat) (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    toComplex (q • a) rep h = (q : ℂ) * toComplex a rep h := by
  change
    (HexPolyMathlib.toPolynomial
      (reduceCoeffs p (DensePoly.scale q a.coeffs))).eval₂
        (algebraMap Rat ℂ) rep.root =
      (q : ℂ) *
        (HexPolyMathlib.toPolynomial a.coeffs).eval₂
          (algebraMap Rat ℂ) rep.root
  rw [eval_reduceCoeffs, HexPolyMathlib.toPolynomial_scale,
    Polynomial.eval₂_mul, Polynomial.eval₂_C]
  exact congrArg
    (fun z : ℂ =>
      z * (HexPolyMathlib.toPolynomial a.coeffs).eval₂
        (algebraMap Rat ℂ) rep.root)
    (map_ratCast (algebraMap Rat ℂ) q)

/-- Fixed-presentation division agrees with complex division. -/
theorem map_div [ZPoly.CheckedIrreducible p] (a b : QAdjoin p x)
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    toComplex (a / b) rep h = toComplex a rep h / toComplex b rep h := by
  sorry

/-- Equality in a checked presentation is exactly equality of interpreted
complex values. -/
theorem eq_iff_toComplex [ZPoly.CheckedIrreducible p]
    (a b : QAdjoin p x) (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = x) :
    a = b ↔ toComplex a rep hrep = toComplex b rep hrep := by
  constructor
  · exact fun h => congrArg (fun value => toComplex value rep hrep) h
  · intro h
    exact @toComplex_injective p x _ rep hrep a b h

end Hex.QAdjoin
