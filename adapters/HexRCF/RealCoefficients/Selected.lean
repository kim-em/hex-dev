/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Field
public import HexNumberFieldMathlib.Exact
public import HexRealFormulaMathlib.Semantics

public section

/-! Reconstruct a canonical algebraic number from a checked selected root. -/

namespace Hex.RCF.RealCoefficients.Selected

open Hex

private theorem cast_root {p q : ZPoly} (h : p = q)
    (r : AlgebraicNumber.OrientedIsolation p) :
    (h ▸ r).rep.root = r.rep.root := by
  cases h
  rfl

@[expose] def algebraic (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.natDegree) (checked : ZPoly.CheckedIrreducible p)
    (squarefree : HasOnlySimpleRoots p) : AlgebraicNumber :=
  AlgebraicNumber.ofNormalized p prim pos_lc pos_degree checked squarefree
    (Field.literalRep p s hw hp)
    (AlgebraicNumber.ofNormalized?_isSome p prim pos_lc pos_degree checked
      squarefree (Field.literalRep p s hw hp))

theorem algebraic_toComplex (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.natDegree) (checked : ZPoly.CheckedIrreducible p)
    (squarefree : HasOnlySimpleRoots p) :
    (algebraic p s hw hp prim pos_lc pos_degree checked squarefree).toComplex =
      (Field.literalRep p s hw hp).root := by
  unfold algebraic AlgebraicNumber.ofNormalized
  let h := AlgebraicNumber.ofNormalized?_isSome p prim pos_lc pos_degree
    checked squarefree (Field.literalRep p s hw hp)
  have hr := AlgebraicNumber.ofNormalized?_toComplex p prim pos_lc pos_degree
    checked squarefree (Field.literalRep p s hw hp) (Option.some_get h).symm
  let a := (AlgebraicNumber.ofNormalized? p prim pos_lc pos_degree checked
    squarefree (Field.literalRep p s hw hp)).get h
  let hpoly : a.p = p := AlgebraicNumber.ofNormalized?_p p prim pos_lc pos_degree
    checked squarefree (Field.literalRep p s hw hp) (Option.some_get h).symm
  change (hpoly ▸ a.isolation).rep.root = _
  exact (cast_root hpoly a.isolation).trans hr

/-- The real version retains the selected complex root, rather than taking
an arbitrary conjugate or projecting a nonreal value. -/
@[expose] def real (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.natDegree) (checked : ZPoly.CheckedIrreducible p)
    (squarefree : HasOnlySimpleRoots p) (hreal : s.meetsRealAxis = true) :
    RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic
    (algebraic p s hw hp prim pos_lc pos_degree checked squarefree) (by
      rw [AlgebraicNumber.isReal_iff, algebraic_toComplex]
      exact Field.literalRep_real p s hw hp hreal)

theorem real_toReal (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.natDegree) (checked : ZPoly.CheckedIrreducible p)
    (squarefree : HasOnlySimpleRoots p) (hreal : s.meetsRealAxis = true) :
    (real p s hw hp prim pos_lc pos_degree checked squarefree hreal).toReal =
      (Field.literalRep p s hw hp).root.re := by
  apply Complex.ofReal_injective
  rw [RealAlgebraicNumber.ofReal_toReal]
  change (algebraic p s hw hp prim pos_lc pos_degree checked squarefree).toComplex = _
  rw [algebraic_toComplex]
  exact Complex.ext rfl (Field.literalRep_real p s hw hp hreal)

/-- Reconstruct a real element from an ordinary computed field coordinate. -/
def field (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.natDegree) (checked : ZPoly.CheckedIrreducible p)
    (squarefree : HasOnlySimpleRoots p) (hreal : s.meetsRealAxis = true)
    (v : QAdjoin (real p s hw hp prim pos_lc pos_degree checked squarefree hreal).toAlgebraic) :
    RealAlgebraicNumber :=
  Coefficients.ofField (real p s hw hp prim pos_lc pos_degree checked squarefree hreal) v

/-- The literal power-basis generator evaluates to the selected real root. -/
theorem generator_value (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true) :
    Field.value (Field.literalRep p s hw hp)
        (PolyQuot.ofSquare p s (DensePoly.ofList [0, 1]) hw hp) =
      (Field.literalRep p s hw hp).root.re := by
  let rep := Field.literalRep p s hw hp
  apply Complex.ofReal_injective
  rw [Field.value_complex rep (Field.literalRep_mk p s hw hp)
    (Field.literalRep_real p s hw hp hreal)]
  change Polynomial.eval₂ (algebraMap ℚ ℂ) rep.root
    (HexPolyMathlib.toPolynomial
      (PolyQuot.reduceCoeffs p (DensePoly.ofList [0, 1]))) =
      ((rep.root.re : ℝ) : ℂ)
  rw [PolyQuot.eval_reduceCoeffs]
  have hX : HexPolyMathlib.toPolynomial (DensePoly.ofList ([0, 1] : List Rat)) =
      Polynomial.X := by
    ext n
    rw [HexPolyMathlib.coeff_toPolynomial, Polynomial.coeff_X]
    simp only [DensePoly.coeff_ofList]
    rcases n with _ | _ | n <;> simp [List.getD]; rfl
  rw [hX, Polynomial.eval₂_X]
  exact Complex.ext rfl (Field.literalRep_real p s hw hp hreal)

/-- Literal fixed-field coordinates retain the value of their unreduced
rational polynomial at the selected root. -/
theorem value_ofSquare (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true) (f : DensePoly Rat) :
    Field.value (Field.literalRep p s hw hp)
        (PolyQuot.ofSquare p s f hw hp) =
      (LiteralSign.realPoly f).eval (Field.literalRep p s hw hp).root.re := by
  let rep := Field.literalRep p s hw hp
  have hpoly : LiteralSign.realPoly f =
      (HexPolyMathlib.toPolynomial f).map (Rat.castHom ℝ) := by
    ext i
    simp [LiteralSign.realPoly]
  apply Complex.ofReal_injective
  rw [Field.value_complex rep (Field.literalRep_mk p s hw hp)
    (Field.literalRep_real p s hw hp hreal)]
  change (HexPolyMathlib.toPolynomial (PolyQuot.reduceCoeffs p f)).eval₂
      (algebraMap Rat ℂ) rep.root =
    (((LiteralSign.realPoly f).eval rep.root.re : ℝ) : ℂ)
  rw [PolyQuot.eval_reduceCoeffs, hpoly, Polynomial.eval_map]
  have he : (rep.root.re : ℂ) = rep.root :=
    Complex.ext rfl (Field.literalRep_real p s hw hp hreal).symm
  calc
    (HexPolyMathlib.toPolynomial f).eval₂ (algebraMap Rat ℂ) rep.root =
        (HexPolyMathlib.toPolynomial f).eval₂
          (Complex.ofRealHom.comp (Rat.castHom ℝ))
          (Complex.ofRealHom rep.root.re) := by rw [← he]; rfl
    _ = Complex.ofRealHom
        ((HexPolyMathlib.toPolynomial f).eval₂ (Rat.castHom ℝ) rep.root.re) :=
      (Polynomial.hom_eval₂ (HexPolyMathlib.toPolynomial f)
        (Rat.castHom ℝ) Complex.ofRealHom rep.root.re).symm

/-- A computed coordinate in the generated field has the value certified by
the literal coordinate polynomial at the same selected root. -/
theorem field_toReal (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.natDegree) (checked : ZPoly.CheckedIrreducible p)
    (squarefree : HasOnlySimpleRoots p) (hreal : s.meetsRealAxis = true)
    (v : QAdjoin (real p s hw hp prim pos_lc pos_degree checked squarefree hreal).toAlgebraic)
    (f : DensePoly Rat) (hcoeff : v.coeffs = f) :
    (field p s hw hp prim pos_lc pos_degree checked squarefree hreal v).toReal =
      Field.value (Field.literalRep p s hw hp)
        (PolyQuot.ofSquare p s f hw hp) := by
  rw [field, Coefficients.ofField_toReal, real_toReal, hcoeff]
  have hmap : LiteralSign.realPoly f =
      (HexPolyMathlib.toPolynomial f).map (Rat.castHom ℝ) := by
    ext i
    simp [LiteralSign.realPoly]
  calc
    (HexPolyMathlib.toPolynomial f).eval₂ (Rat.castHom ℝ)
        (Field.literalRep p s hw hp).root.re =
        (LiteralSign.realPoly f).eval (Field.literalRep p s hw hp).root.re := by
      rw [hmap, Polynomial.eval_map]
    _ = _ := (value_ofSquare p s hw hp hreal f).symm

theorem valuation (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.natDegree) (checked : ZPoly.CheckedIrreducible p)
    (squarefree : HasOnlySimpleRoots p) (hreal : s.meetsRealAxis = true)
    (values : Fin 1 → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (hvalue : values 0 = PolyQuot.ofSquare p s (DensePoly.ofList [0, 1]) hw hp) :
    (fun i => Field.value (Field.literalRep p s hw hp) (values i)) =
      Hex.RealFormula.append Fin.elim0
        (real p s hw hp prim pos_lc pos_degree checked squarefree hreal).toReal := by
  funext i
  fin_cases i
  simpa [hvalue, Hex.RealFormula.append] using
    (generator_value p s hw hp hreal).trans
      (real_toReal p s hw hp prim pos_lc pos_degree checked squarefree hreal).symm

theorem field_valuation (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.natDegree) (checked : ZPoly.CheckedIrreducible p)
    (squarefree : HasOnlySimpleRoots p) (hreal : s.meetsRealAxis = true)
    (v : QAdjoin (real p s hw hp prim pos_lc pos_degree checked squarefree hreal).toAlgebraic)
    (f : DensePoly Rat) (hcoeff : v.coeffs = f)
    (values : Fin 1 → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (hvalue : values 0 = PolyQuot.ofSquare p s f hw hp) :
    (fun i => Field.value (Field.literalRep p s hw hp) (values i)) =
      Hex.RealFormula.append Fin.elim0
        (field p s hw hp prim pos_lc pos_degree checked squarefree hreal v).toReal := by
  funext i
  fin_cases i
  simpa [hvalue, Hex.RealFormula.append] using
    (field_toReal p s hw hp prim pos_lc pos_degree checked squarefree hreal v f hcoeff).symm

end Hex.RCF.RealCoefficients.Selected
