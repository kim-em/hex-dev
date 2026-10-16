/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.CommonPresentation
public import HexRealClosureTheory.TowerModel
public import HexRealClosureTheory.SignFacts
public import HexPolyTheory.Interpret

public section

/-! Source identities at a fixed ordinary-real interpretation. The actual
coefficient-map equalities, source root selection and sign observations are
proof inputs obtained from literal replay; these lemmas do not run producers
or supply those checked facts. No identity of computed proposals is assumed. -/

namespace Hex.RCF.RealCoefficients.SourceIdentity
open Hex Hex.RealClosure

/-- The rational polynomial whose positive sign selects the interior of a
source isolating disc on the real axis. -/
@[expose] def margin (square : DyadicSquare) : DensePoly Rat :=
  DensePoly.ofCoeffs #[2 * square.halfWidth.toRat ^ 2 - square.im.toRat ^ 2 -
    square.re.toRat ^ 2, 2 * square.re.toRat, -1]

theorem margin_eval (square : DyadicSquare) (x : ℝ) :
    (LiteralSign.realPoly (margin square)).eval x =
      2 * (square.halfWidth.toRat : ℝ)^2 - (square.im.toRat : ℝ)^2 -
        (x - (square.re.toRat : ℝ))^2 := by
  unfold margin LiteralSign.realPoly
  rw [HexPolyTheory.Interpret.interpret_map, DensePoly.Interpret.map_ofCoeffs,
    HexPolyTheory.toPolynomial_ofCoeffs]
  simp [Finset.sum_range_succ, Array.getD]
  ring

/-- Read a scalar sign at this exact native selected root, binding its
polynomial coefficientwise to the rational source query. -/
theorem observe {registry : BaseContext.Registry} {parent : Tower.Context registry}
    (model : Tower.Model parent ℝ)
    (root : SignDet.Descriptor parent.Value Tower.Signature parent.sign parent.signature)
    (p : DensePoly parent.Value) (q : DensePoly Rat)
    (coefficients : HexPolyTheory.Interpret.interpret model.value model.zero_iff p =
      LiteralSign.realPoly q)
    (fact : Algebraic.SignFact (Algebraic.Context.adjoin root parent.isClean))
    (binding : fact.polynomial = p) :
    (SignType.sign ((LiteralSign.realPoly q).eval (root.root model.value model.zero_iff
      model.one model.add model.sub model.mul model.nat model.sign)) : Int) = fact.sign := by
  have checked := fact.checked
  rw [binding, Algebraic.Context.signPoly_spec model.value model.zero_iff model.one
    model.add model.sub model.mul model.nat model.sign model.neg model.inv _ p] at checked
  simpa only [Algebraic.Context.evalPoly, Algebraic.Context.rootValue, Algebraic.Context.root_adjoin, coefficients] using checked

/-- The existing operation-only polynomial transport reads a literal source
coordinate at the model's value. The map equality binds every coefficient. -/
theorem evaluate {registry : BaseContext.Registry} {context : Tower.Context registry}
    (model : Tower.Model context ℝ) (p : DensePoly context.Value) (q : DensePoly Rat)
    (coefficients : HexPolyTheory.toPolynomial
      (DensePoly.Interpret.map model.value model.zero_iff p) = LiteralSign.realPoly q)
    (x : context.Value) :
    model.value (p.eval x) = (LiteralSign.realPoly q).eval (model.value x) := by
  rw [DensePoly.Interpret.map_eval model.value model.zero_iff model.add model.mul]
  rw [← HexPolyTheory.eval_toPolynomial, coefficients]

/-- A checked native zero sign proves the source equation at this same value. -/
theorem equation {registry : BaseContext.Registry} {context : Tower.Context registry}
    (model : Tower.Model context ℝ) (p : DensePoly context.Value) (q : DensePoly Rat)
    (coefficients : HexPolyTheory.toPolynomial
      (DensePoly.Interpret.map model.value model.zero_iff p) = LiteralSign.realPoly q)
    (x : context.Value) (observed : context.sign (p.eval x) = 0) :
    (LiteralSign.realPoly q).IsRoot (model.value x) := by
  have code := (model.sign (p.eval x)).symm.trans observed
  have zero : model.value (p.eval x) = 0 := by
    apply sign_eq_zero_iff.mp
    cases tagged : SignType.sign (model.value (p.eval x)) <;> simp_all
  rw [evaluate model p q coefficients x] at zero
  exact zero

/-- A checked positive sign proves the source-selection margin at this value. -/
theorem positive {registry : BaseContext.Registry} {context : Tower.Context registry}
    (model : Tower.Model context ℝ) (p : DensePoly context.Value) (q : DensePoly Rat)
    (coefficients : HexPolyTheory.toPolynomial
      (DensePoly.Interpret.map model.value model.zero_iff p) = LiteralSign.realPoly q)
    (x : context.Value) (observed : context.sign (p.eval x) = 1) :
    0 < (LiteralSign.realPoly q).eval (model.value x) := by
  have code := (model.sign (p.eval x)).symm.trans observed
  have sign : SignType.sign (model.value (p.eval x)) = 1 := by
    cases tagged : SignType.sign (model.value (p.eval x)) <;> simp_all
  have greater := sign_eq_one_iff.mp sign
  rwa [evaluate model p q coefficients x] at greater

/-- A source equation and a positive enclosure margin identify the selected
source value independently of the carrier used by the checker. -/
theorem select (sourceP : ZPoly) (square : DyadicSquare)
    (hw : atomWitness sourceP square) (hp : (mahlerPrec sourceP : Int) ≤ square.prec)
    (anchor x : ℝ)
    (selected : (Field.literalRep sourceP square hw hp).root.re = anchor)
    (zero : (LiteralSign.realPoly (ZPoly.toRatPoly sourceP)).IsRoot x)
    (inside : 0 < 2 * (square.halfWidth.toRat : ℝ)^2 -
      (square.im.toRat : ℝ)^2 - (x - (square.re.toRat : ℝ))^2) :
    x = anchor := by
  have root := CommonPresentation.root_complex sourceP x zero
  have disc := CommonPresentation.mem_disc square x inside
  have same := HexRootsTheory.RefinedIsolation.eq_root_of_mem_closedDisc
    (Field.literalRep sourceP square hw hp) root disc
  have realPart := congrArg Complex.re same
  simpa only [Complex.ofReal_re, selected] using realPart

end Hex.RCF.RealCoefficients.SourceIdentity
