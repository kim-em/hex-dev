/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField
public import HexResultantMathlib
public import HexBerlekampZassenhausMathlib
public import HexRootsMathlib
public import HexPolyZMathlib
public import Mathlib.FieldTheory.Minpoly.Field

public section

/-!
# Semantic interpretation of executable algebraic numbers

This module fixes the complex value represented by every selected isolation and
the evaluation map for a checked fixed presentation. Separate modules state
the algebraic laws and completeness results over this semantic boundary.
-/

namespace Hex

/-- A computationally checked irreducible integer polynomial remains
irreducible after extension of coefficients to the rationals. -/
theorem ZPoly.CheckedIrreducible.irreducibleRat (p : ZPoly)
    [ZPoly.CheckedIrreducible p] :
    _root_.Irreducible (HexPolyZMathlib.toPolyℚ p) := by
  have hirrZ : _root_.Irreducible (HexPolyZMathlib.toPolynomial p) :=
    (HexBerlekampZassenhausMathlib.Hex.ZPoly.Irreducible_iff_polynomialIrreducible p).mp <|
      (HexBerlekampZassenhausMathlib.Hex.ZPoly.isIrreducible_iff p).mp
        (ZPoly.CheckedIrreducible.is_true (p := p))
  have hdegree : (HexPolyZMathlib.toPolynomial p).natDegree ≠ 0 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    exact Nat.ne_of_gt (ZPoly.CheckedIrreducible.pos_degree (p := p))
  have hprimitive : (HexPolyZMathlib.toPolynomial p).IsPrimitive :=
    hirrZ.isPrimitive hdegree
  exact
    ((Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      hprimitive).mp hirrZ)

/-- A computationally checked irreducible integer polynomial is separable over
the rationals. The factorization correspondence supplies irreducibility; this
is the semantic bridge used by quotient-root interpretation. -/
theorem ZPoly.CheckedIrreducible.separable (p : ZPoly)
    [ZPoly.CheckedIrreducible p] :
    (HexPolyZMathlib.toPolyℚ p).Separable := by
  exact (ZPoly.CheckedIrreducible.irreducibleRat p).separable

namespace AlgebraicRoot

/-- The complex value selected by a factorization-lazy algebraic root. -/
@[expose]
noncomputable def toComplex (a : AlgebraicRoot) : ℂ :=
  a.rep.root

/-- The selected value zeros the enclosing integer polynomial. -/
theorem toComplex_isRoot (a : AlgebraicRoot) :
    (HexRootsMathlib.toPolyℂ a.p).eval a.toComplex = 0 := by
  exact HexRootsMathlib.RefinedIsolation.isRoot a.rep

end AlgebraicRoot

namespace AlgebraicNumber

/-- The complex value selected by a canonical algebraic number. -/
@[expose]
noncomputable def toComplex (a : AlgebraicNumber) : ℂ :=
  a.rep.root

/-- A canonical algebraic number stores its primitive positive associate of the
rational minimal polynomial. -/
theorem p_eq_minpoly (a : AlgebraicNumber) :
    (a.p.leadingCoeff : Rat)⁻¹ • HexPolyZMathlib.toPolyℚ a.p =
      minpoly Rat a.toComplex := by
  letI : ZPoly.CheckedIrreducible a.p := a.checked
  have hroot :
      Polynomial.aeval a.toComplex (HexPolyZMathlib.toPolyℚ a.p) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    have hcomp :
        (algebraMap Rat ℂ).comp (Int.castRingHom Rat) =
          Int.castRingHom ℂ :=
      RingHom.ext_int _ _
    rw [show
        (HexPolyZMathlib.toPolyℚ a.p).map (algebraMap Rat ℂ) =
          HexRootsMathlib.toPolyℂ a.p by
      dsimp [HexPolyZMathlib.toPolyℚ, HexRootsMathlib.toPolyℂ]
      rw [Polynomial.map_map, hcomp]]
    exact AlgebraicRoot.toComplex_isRoot a.toRoot
  have hmin := minpoly.eq_of_irreducible
    (ZPoly.CheckedIrreducible.irreducibleRat a.p) hroot
  have hlc :
      (HexPolyZMathlib.toPolyℚ a.p).leadingCoeff =
        (a.p.leadingCoeff : Rat) := by
    rw [HexPolyZMathlib.toPolyℚ,
      Polynomial.leadingCoeff_map_of_injective
        (RingHom.injective_int (Int.castRingHom Rat)),
      HexPolyMathlib.leadingCoeff_toPolynomial]
    rfl
  rw [hlc] at hmin
  simpa [Polynomial.smul_eq_C_mul, mul_comm] using hmin

end AlgebraicNumber

namespace QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

/-- Evaluate canonical fixed-field coordinates at their selected complex root.
The representative and quotient equality are explicit inputs so this semantic
map does not depend on an irreducibility proof. -/
@[expose]
noncomputable def toComplex (a : QAdjoin p x)
    (rep : RefinedIsolation p) (_h : SimpleRoot.mk rep = x) : ℂ :=
  (HexPolyMathlib.toPolynomial a.coeffs).eval₂ (algebraMap Rat ℂ)
    rep.root

/-- Reduction modulo the defining polynomial preserves evaluation at the
selected root. -/
theorem eval_reduceCoeffs (f : DensePoly Rat)
    (rep : RefinedIsolation p) :
    (HexPolyMathlib.toPolynomial (reduceCoeffs p f)).eval₂
        (algebraMap Rat ℂ) rep.root =
      (HexPolyMathlib.toPolynomial f).eval₂
        (algebraMap Rat ℂ) rep.root := by
  have hp :
      (HexPolyMathlib.toPolynomial (ZPoly.toRatPoly p)).eval₂
          (algebraMap Rat ℂ) rep.root = 0 := by
    rw [HexPolyZMathlib.toPolynomial_toRatPoly,
      Polynomial.eval₂_eq_eval_map]
    have hcomp :
        (algebraMap Rat ℂ).comp (Int.castRingHom Rat) =
          Int.castRingHom ℂ :=
      RingHom.ext_int _ _
    rw [show
        (HexPolyZMathlib.toPolyℚ p).map (algebraMap Rat ℂ) =
          HexRootsMathlib.toPolyℂ p by
      dsimp [HexPolyZMathlib.toPolyℚ, HexRootsMathlib.toPolyℂ]
      rw [Polynomial.map_map, hcomp]]
    exact HexRootsMathlib.RefinedIsolation.isRoot rep
  have hdiv := congrArg
    (fun g : DensePoly Rat =>
      (HexPolyMathlib.toPolynomial g).eval₂
        (algebraMap Rat ℂ) rep.root)
    (DensePoly.div_mul_add_mod f (ZPoly.toRatPoly p))
  simpa only [reduceCoeffs, HexPolyMathlib.toPolynomial_add,
    HexPolyMathlib.toPolynomial_mul, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, hp, mul_zero, zero_add] using hdiv

/-- Fixed-presentation addition agrees with complex addition. -/
theorem map_add (a b : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    toComplex (a + b) rep h = toComplex a rep h + toComplex b rep h := by
  change
    (HexPolyMathlib.toPolynomial
      (reduceCoeffs p (a.coeffs + b.coeffs))).eval₂
        (algebraMap Rat ℂ) rep.root =
      (HexPolyMathlib.toPolynomial a.coeffs).eval₂
          (algebraMap Rat ℂ) rep.root +
        (HexPolyMathlib.toPolynomial b.coeffs).eval₂
          (algebraMap Rat ℂ) rep.root
  rw [eval_reduceCoeffs, HexPolyMathlib.toPolynomial_add,
    Polynomial.eval₂_add]

/-- Fixed-presentation multiplication agrees with complex multiplication. -/
theorem map_mul (a b : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    toComplex (a * b) rep h = toComplex a rep h * toComplex b rep h := by
  change
    (HexPolyMathlib.toPolynomial
      (reduceCoeffs p (a.coeffs * b.coeffs))).eval₂
        (algebraMap Rat ℂ) rep.root =
      (HexPolyMathlib.toPolynomial a.coeffs).eval₂
          (algebraMap Rat ℂ) rep.root *
        (HexPolyMathlib.toPolynomial b.coeffs).eval₂
          (algebraMap Rat ℂ) rep.root
  rw [eval_reduceCoeffs, HexPolyMathlib.toPolynomial_mul,
    Polynomial.eval₂_mul]

end QAdjoin

/-- Canonical Boolean equality is equality of represented complex values. -/
theorem AlgebraicNumber.beq_iff (a b : AlgebraicNumber) :
    (a == b) ↔ a.toComplex = b.toComplex := by
  sorry

/-- The executable zero predicate recognizes exactly the complex value zero. -/
theorem AlgebraicRoot.isZero_iff (a : AlgebraicRoot) :
    a.isZero ↔ a.toComplex = 0 := by
  sorry

/-- The canonical algebraic-number zero test recognizes exactly complex zero. -/
theorem AlgebraicNumber.isZero_iff (a : AlgebraicNumber) :
    a.isZero ↔ a.toComplex = 0 := by
  sorry

end Hex
