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

private def RefinedIsolation.castPoly {p q : ZPoly} (h : p = q)
    (r : RefinedIsolation q) : RefinedIsolation p :=
  h.symm ▸ r

private theorem RefinedIsolation.castPoly_square {p q : ZPoly} (h : p = q)
    (r : RefinedIsolation q) :
    (r.castPoly h).1.square = r.1.square := by
  cases h
  rfl

private theorem RefinedIsolation.castPoly_root {p q : ZPoly} (h : p = q)
    (r : RefinedIsolation q) :
    (r.castPoly h).root = r.root := by
  cases h
  rfl

private theorem AlgebraicNumber.eq_polynomial {a b : AlgebraicNumber}
    (h : a.toComplex = b.toComplex) : a.p = b.p := by
  have hscaled :
      Polynomial.C (a.p.leadingCoeff : Rat)⁻¹ *
          HexPolyZMathlib.toPolyℚ a.p =
        Polynomial.C (b.p.leadingCoeff : Rat)⁻¹ *
          HexPolyZMathlib.toPolyℚ b.p := by
    simpa [Polynomial.smul_eq_C_mul] using
      (AlgebraicNumber.p_eq_minpoly a).trans
        ((congrArg (minpoly Rat) h).trans
          (AlgebraicNumber.p_eq_minpoly b).symm)
  have halc : (a.p.leadingCoeff : Rat) ≠ 0 := by
    exact_mod_cast (ne_of_gt a.pos_lc)
  have hblc : (b.p.leadingCoeff : Rat) ≠ 0 := by
    exact_mod_cast (ne_of_gt b.pos_lc)
  have haunit : IsUnit (Polynomial.C (a.p.leadingCoeff : Rat)⁻¹) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero halc))
  have hbunit : IsUnit (Polynomial.C (b.p.leadingCoeff : Rat)⁻¹) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hblc))
  have hrat : Associated (HexPolyZMathlib.toPolyℚ a.p)
      (HexPolyZMathlib.toPolyℚ b.p) :=
    (associated_unit_mul_left _ _ haunit).symm |>.trans <|
      (Associated.of_eq hscaled).trans (associated_unit_mul_left _ _ hbunit)
  have haprim := HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive a.p a.prim
  have hbprim := HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive b.p b.prim
  have hint : Associated (HexPolyZMathlib.toPolynomial a.p)
      (HexPolyZMathlib.toPolynomial b.p) :=
    dvd_dvd_iff_associated.mp ⟨
      (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ haprim hbprim).mpr
        hrat.dvd,
      (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ hbprim haprim).mpr
        hrat.symm.dvd⟩
  exact
    HexBerlekampZassenhausMathlib.zpoly_eq_of_toPolynomial_associated_of_primitive_pos_leading
        a.prim b.prim a.pos_lc b.pos_lc hint

/-- Canonical zero denotes complex zero. -/
@[simp] theorem AlgebraicNumber.zero_toComplex :
    (0 : AlgebraicNumber).toComplex = 0 := by
  have hroot := AlgebraicRoot.toComplex_isRoot
    (0 : AlgebraicNumber).toRoot
  change (HexRootsMathlib.toPolyℂ (0 : AlgebraicNumber).p).eval
    (0 : AlgebraicNumber).toComplex = 0 at hroot
  rw [AlgebraicNumber.zero_p] at hroot
  simpa [HexRootsMathlib.toPolyℂ, ZPoly.X] using hroot

/-- Successful canonicalization preserves the complex root selected by the
supplied refined isolation, including the explicit canonical-zero path. -/
theorem AlgebraicNumber.ofNormalized?_toComplex
    (p : ZPoly) (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.degree?.getD 0)
    (checked : ZPoly.CheckedIrreducible p) (squarefree : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) {a : AlgebraicNumber}
    (h : AlgebraicNumber.ofNormalized? p prim pos_lc pos_degree checked
      squarefree rep = some a) :
    a.toComplex = rep.root := by
  rcases AlgebraicNumber.ofNormalized?_spec p prim pos_lc pos_degree checked
      squarefree rep h with hzero | hinter
  · rcases hzero with ⟨hp, rfl⟩
    subst p
    rw [AlgebraicNumber.zero_toComplex]
    have hroot : rep.root = 0 := by
      simpa [HexRootsMathlib.toPolyℂ, ZPoly.X] using
        HexRootsMathlib.RefinedIsolation.isRoot rep
    exact hroot.symm
  · obtain ⟨hp, hinter⟩ := hinter
    let arep : RefinedIsolation p := hp ▸ a.rep
    have haroot : arep.root = a.rep.root := by
      cases hp
      rfl
    have hpne : p ≠ 0 := by
      intro hp0
      rw [hp0] at pos_degree
      simp at pos_degree
    have hroot :=
      (HexRootsMathlib.RefinedIsolation.intersects_iff_root_eq_of_simple
        squarefree hpne arep rep).mp hinter
    change a.rep.root = rep.root
    rw [← haroot]
    exact hroot

/-- Canonical Boolean equality is equality of represented complex values. -/
theorem AlgebraicNumber.beq_iff (a b : AlgebraicNumber) :
    (a == b) ↔ a.toComplex = b.toComplex := by
  change AlgebraicNumber.beq a b = true ↔ a.toComplex = b.toComplex
  rw [AlgebraicNumber.beq]
  rw [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hp, hmeet⟩
    let brep : RefinedIsolation a.p := b.rep.castPoly hp
    letI : ZPoly.CheckedIrreducible a.p := a.checked
    have hinter : Intersects a.rep brep := by
      change a.rep.1.square.discsMeet brep.1.square = true
      rw [show brep.1.square = b.rep.1.square by
        exact RefinedIsolation.castPoly_square hp b.rep]
      exact hmeet
    have hroot :=
      (HexRootsMathlib.RefinedIsolation.intersects_iff_root_eq
        (ZPoly.CheckedIrreducible.separable a.p) a.rep brep).mp hinter
    change a.rep.root = b.rep.root
    rw [← RefinedIsolation.castPoly_root hp b.rep]
    exact hroot
  · intro hroot
    have hp := AlgebraicNumber.eq_polynomial hroot
    refine ⟨hp, ?_⟩
    let brep : RefinedIsolation a.p := b.rep.castPoly hp
    letI : ZPoly.CheckedIrreducible a.p := a.checked
    have hroot' : a.rep.root = brep.root := by
      rw [show brep.root = b.rep.root by
        exact RefinedIsolation.castPoly_root hp b.rep]
      exact hroot
    have hinter : Intersects a.rep brep :=
      (HexRootsMathlib.RefinedIsolation.intersects_iff_root_eq
        (ZPoly.CheckedIrreducible.separable a.p) a.rep brep).mpr hroot'
    change a.rep.1.square.discsMeet b.rep.1.square = true
    change a.rep.1.square.discsMeet brep.1.square = true at hinter
    rw [show brep.1.square = b.rep.1.square by
      exact RefinedIsolation.castPoly_square hp b.rep] at hinter
    exact hinter

/-- The executable zero predicate recognizes exactly the complex value zero. -/
theorem AlgebraicRoot.isZero_iff (a : AlgebraicRoot) :
    a.isZero ↔ a.toComplex = 0 := by
  rw [AlgebraicRoot.isZero, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hcoeff, hcontains⟩
    have hzeroRoot : (HexRootsMathlib.toPolyℂ a.p).IsRoot 0 := by
      change (HexRootsMathlib.toPolyℂ a.p).eval 0 = 0
      rw [← Polynomial.coeff_zero_eq_eval_zero,
        HexRootsMathlib.coeff_toPolyℂ, hcoeff]
      simp
    have hzeroMem :
        (0 : ℂ) ∈ HexRootsMathlib.DyadicSquare.closedDisc a.rep.1.square := by
      have hmem :=
        (HexRootsMathlib.DyadicSquare.discContains_iff_mem_closedDisc
          a.rep.1.square (0, 0)).mp hcontains
      simp at hmem
      exact hmem
    have hpne : a.p ≠ 0 := by
      intro hp
      have hpos := a.pos_degree
      rw [hp] at hpos
      simp at hpos
    have hroot :=
      HexRootsMathlib.RefinedIsolation.eq_root_of_mem_closedDisc
        (HexRootsMathlib.HasOnlySimpleRoots.separable a.squarefree hpne)
        a.rep hzeroRoot hzeroMem
    exact hroot.symm
  · intro hroot
    have hpolyRoot := AlgebraicRoot.toComplex_isRoot a
    have hcoeffComplex : (a.p.coeff 0 : ℂ) = 0 := by
      rw [hroot] at hpolyRoot
      rw [← Polynomial.coeff_zero_eq_eval_zero,
        HexRootsMathlib.coeff_toPolyℂ] at hpolyRoot
      exact hpolyRoot
    have hcoeff : a.p.coeff 0 = 0 := by
      exact_mod_cast hcoeffComplex
    refine ⟨hcoeff, ?_⟩
    have hmem := HexRootsMathlib.RefinedIsolation.root_mem_closedDisc a.rep
    change a.toComplex ∈
      HexRootsMathlib.DyadicSquare.closedDisc a.rep.1.square at hmem
    rw [hroot] at hmem
    apply
      (HexRootsMathlib.DyadicSquare.discContains_iff_mem_closedDisc
        a.rep.1.square (0, 0)).mpr
    simp
    exact hmem

/-- The canonical algebraic-number zero test recognizes exactly complex zero. -/
theorem AlgebraicNumber.isZero_iff (a : AlgebraicNumber) :
    a.isZero ↔ a.toComplex = 0 := by
  rw [AlgebraicNumber.isZero, beq_iff_eq]
  constructor
  · intro hp
    have hroot := AlgebraicRoot.toComplex_isRoot a.toRoot
    change (HexRootsMathlib.toPolyℂ a.p).eval a.toComplex = 0 at hroot
    rw [hp] at hroot
    simpa [HexRootsMathlib.toPolyℂ, ZPoly.X] using hroot
  · intro hroot
    have hp := AlgebraicNumber.eq_polynomial
      (hroot.trans AlgebraicNumber.zero_toComplex.symm)
    simpa [AlgebraicNumber.zero_p] using hp

end Hex
