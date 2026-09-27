/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Field

public section

/-!
A proposed coordinate in a common field must denote the selected source root.
The source polynomial equation by itself is insufficient: the source's
certified square distinguishes its chosen root from its conjugates.
-/

namespace Hex.RCF.RealCoefficients.CommonPresentation

/-- Evaluate a rational polynomial at a common-field coordinate using only
the existing total reduced-coordinate operations. -/
@[expose] def evalAt {p : ZPoly} {root : SimpleRoot p}
    (f : DensePoly Rat) (v : PolyQuot p root) : PolyQuot p root :=
  DensePoly.evalCoeffList (f.toArray.toList.map PolyQuot.ofRat) v

private theorem value_ofRat {p : ZPoly} {s : DyadicSquare}
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true) (q : Rat) :
    Field.value (Field.literalRep p s hw hp)
      (PolyQuot.ofRat q : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) =
        (q : ℝ) := by
  apply Complex.ofReal_injective
  rw [Field.value_complex (Field.literalRep p s hw hp)
    (Field.literalRep_mk p s hw hp)
    (Field.literalRep_real p s hw hp hreal)]
  change PolyQuot.toComplex (q • (1 : PolyQuot p
    (SimpleRoot.ofSquare p s hw hp)))
      (Field.literalRep p s hw hp) (Field.literalRep_mk p s hw hp) = (q : ℂ)
  rw [PolyQuot.map_smul, PolyQuot.map_one, mul_one]

private theorem evalList_value {p : ZPoly} {s : DyadicSquare}
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true) (cs : List Rat)
    (v : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) :
    Field.value (Field.literalRep p s hw hp)
      (DensePoly.evalCoeffList (cs.map PolyQuot.ofRat) v) =
    DensePoly.evalCoeffList (cs.map (fun (q : Rat) => (q : ℝ)))
      (Field.value (Field.literalRep p s hw hp) v) := by
  induction cs with
  | nil =>
      exact Field.value_zero (Field.literalRep p s hw hp)
        (Field.literalRep_mk p s hw hp)
        (Field.literalRep_real p s hw hp hreal)
  | cons c cs ih =>
      simp only [List.map_cons, DensePoly.evalCoeffList]
      rw [Field.value_add (Field.literalRep p s hw hp)
          (Field.literalRep_mk p s hw hp)
          (Field.literalRep_real p s hw hp hreal),
        Field.value_mul (Field.literalRep p s hw hp)
          (Field.literalRep_mk p s hw hp)
          (Field.literalRep_real p s hw hp hreal),
        ih, value_ofRat hw hp hreal]

/-- The total Horner computation evaluates to the same real value at the
selected common-field root. -/
theorem evalAt_value {p : ZPoly} {s : DyadicSquare}
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true) (f : DensePoly Rat)
    (v : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) :
    Field.value (Field.literalRep p s hw hp) (evalAt f v) =
      DensePoly.evalCoeffList (f.toArray.toList.map (fun (q : Rat) => (q : ℝ)))
        (Field.value (Field.literalRep p s hw hp) v) :=
  evalList_value hw hp hreal f.toArray.toList v

/-- The finite real Horner expression is the ordinary polynomial evaluation
used to state the source equation. -/
theorem horner_realPoly (f : DensePoly Rat) (x : ℝ) :
    DensePoly.evalCoeffList (f.toArray.toList.map (fun (q : Rat) => (q : ℝ))) x =
      (LiteralSign.realPoly f).eval x := by
  have hpoly : LiteralSign.realPoly f =
      (HexPolyMathlib.toPolynomial f).map (Rat.castHom ℝ) := by
    ext i
    simp [LiteralSign.realPoly]
  rw [hpoly, Polynomial.eval_map,
    HexPolyMathlib.eval₂_horner (Rat.castHom ℝ) f x]
  change DensePoly.evalCoeffList
      (f.toArray.toList.map (fun (q : Rat) => (q : ℝ))) x =
    f.toArray.toList.foldr (fun (c : Rat) (acc : ℝ) => (c : ℝ) + x * acc) 0
  generalize f.toArray.toList = cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp [DensePoly.evalCoeffList, ih, mul_comm, add_comm]

theorem evalAt_realPoly {p : ZPoly} {s : DyadicSquare}
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true) (f : DensePoly Rat)
    (v : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) :
    Field.value (Field.literalRep p s hw hp) (evalAt f v) =
      (LiteralSign.realPoly f).eval
        (Field.value (Field.literalRep p s hw hp) v) := by
  rw [evalAt_value hw hp hreal, horner_realPoly]

private theorem realPoly_root_complex (q : ZPoly) (x : ℝ)
    (hroot : (LiteralSign.realPoly (ZPoly.toRatPoly q)).IsRoot x) :
    (HexRootsMathlib.toPolyℂ q).IsRoot (x : ℂ) := by
  have hpoly : (LiteralSign.realPoly (ZPoly.toRatPoly q)).map Complex.ofRealHom =
      HexRootsMathlib.toPolyℂ q := by
    ext i
    simp [LiteralSign.realPoly, HexRootsMathlib.toPolyℂ]
  change (HexRootsMathlib.toPolyℂ q).eval (x : ℂ) = 0
  rw [← hpoly, Polynomial.eval_map]
  change (LiteralSign.realPoly (ZPoly.toRatPoly q)).eval₂
    Complex.ofRealHom (Complex.ofRealHom x) = 0
  rw [Polynomial.eval₂_at_apply]
  exact map_zero Complex.ofRealHom ▸ congrArg Complex.ofRealHom hroot

/-- Check a source polynomial equation by total arithmetic in the proposed
common field. This checks zero directly in reduced rational coordinates. -/
@[expose] def checkEquation {p : ZPoly} {root : SimpleRoot p}
    (sourcePolynomial : DensePoly Rat) (v : PolyQuot p root) : Bool :=
  decide (evalAt sourcePolynomial v = 0)

/-- A passing finite equation check proves the source polynomial equation at
the coordinate's real value. Root selection needs the separate enclosure
check below. -/
theorem checkEquation_sound {p : ZPoly} {s : DyadicSquare}
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true)
    (sourcePolynomial : DensePoly Rat)
    (v : PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (accepted : checkEquation sourcePolynomial v = true) :
    (LiteralSign.realPoly sourcePolynomial).IsRoot
      (Field.value (Field.literalRep p s hw hp) v) := by
  have heq : evalAt sourcePolynomial v = 0 :=
    of_decide_eq_true accepted
  have hvalue := congrArg (Field.value (Field.literalRep p s hw hp)) heq
  rw [evalAt_realPoly hw hp hreal,
    Field.value_zero (Field.literalRep p s hw hp)
      (Field.literalRep_mk p s hw hp)
      (Field.literalRep_real p s hw hp hreal)] at hvalue
  exact hvalue

/-- The squared-radius margin for placing a real coordinate in a source
isolation's complex disc. All constants are rational dyadics. -/
@[expose] def discSlack {p : ZPoly} {root : SimpleRoot p}
    (sourceSquare : DyadicSquare) (v : PolyQuot p root) : PolyQuot p root :=
  let re := sourceSquare.re.toRat
  let im := sourceSquare.im.toRat
  let width := sourceSquare.halfWidth.toRat
  PolyQuot.ofRat (2 * width ^ 2 - im ^ 2) -
    (v - PolyQuot.ofRat re) * (v - PolyQuot.ofRat re)

theorem discSlack_value {p : ZPoly} {s : DyadicSquare}
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true) (sourceSquare : DyadicSquare)
    (v : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) :
    Field.value (Field.literalRep p s hw hp) (discSlack sourceSquare v) =
      (2 * (sourceSquare.halfWidth.toRat : ℝ) ^ 2 -
        (sourceSquare.im.toRat : ℝ) ^ 2) -
      (Field.value (Field.literalRep p s hw hp) v -
        (sourceSquare.re.toRat : ℝ)) ^ 2 := by
  unfold discSlack
  rw [Field.value_sub (Field.literalRep p s hw hp)
      (Field.literalRep_mk p s hw hp)
      (Field.literalRep_real p s hw hp hreal),
    Field.value_mul (Field.literalRep p s hw hp)
      (Field.literalRep_mk p s hw hp)
      (Field.literalRep_real p s hw hp hreal),
    value_ofRat hw hp hreal,
    Field.value_sub (Field.literalRep p s hw hp)
      (Field.literalRep_mk p s hw hp)
      (Field.literalRep_real p s hw hp hreal),
    value_ofRat hw hp hreal]
  push_cast
  ring

private theorem in_disc_of_slack (sourceSquare : DyadicSquare) (x : ℝ)
    (hslack : 0 < 2 * (sourceSquare.halfWidth.toRat : ℝ) ^ 2 -
      (sourceSquare.im.toRat : ℝ) ^ 2 -
      (x - (sourceSquare.re.toRat : ℝ)) ^ 2) :
    (x : ℂ) ∈ HexRootsMathlib.DyadicSquare.closedDisc sourceSquare := by
  let z : ℂ := (x : ℂ) - HexRootsMathlib.DyadicSquare.center sourceSquare
  have hre : z.re = x - (sourceSquare.re.toRat : ℝ) := by
    simp [z, HexRootsMathlib.DyadicSquare.center_eq,
      Hex.DyadicSquare.center, HexRootsMathlib.Dyadic.toReal]
  have him : z.im = -(sourceSquare.im.toRat : ℝ) := by
    simp [z, HexRootsMathlib.DyadicSquare.center_eq,
      Hex.DyadicSquare.center, HexRootsMathlib.Dyadic.toReal]
  have hwidth : (sourceSquare.halfWidth.toRat : ℝ) =
      HexRootsMathlib.DyadicSquare.halfWidth sourceSquare := by
    change HexRootsMathlib.Dyadic.toReal sourceSquare.halfWidth = _
    simp [Hex.DyadicSquare.halfWidth]
  have hradiusWidth : HexRootsMathlib.DyadicSquare.radius sourceSquare =
      (sourceSquare.halfWidth.toRat : ℝ) * Real.sqrt 2 := by
    rw [HexRootsMathlib.DyadicSquare.radius_eq,
      ← HexRootsMathlib.DyadicSquare.halfWidth_eq, ← hwidth]
  have hsq : ‖z‖ ^ 2 <
      HexRootsMathlib.DyadicSquare.radius sourceSquare ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him,
      hradiusWidth]
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    nlinarith
  have hradius : 0 ≤ HexRootsMathlib.DyadicSquare.radius sourceSquare := by
    rw [HexRootsMathlib.DyadicSquare.radius_eq]
    positivity
  have hdist : ‖z‖ < HexRootsMathlib.DyadicSquare.radius sourceSquare := by
    nlinarith [norm_nonneg z]
  apply Metric.mem_closedBall.mpr
  simpa only [dist_eq_norm] using le_of_lt hdist

/-- Verify an enclosure by a recorded positive sign for the squared-radius
margin. The sign table is bound to the literal common generator and square. -/
@[expose] def checkDisc {p : ZPoly} {s : DyadicSquare}
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table
      (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (sourceSquare : DyadicSquare)
    (v : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) : Bool :=
  Field.checkSignTable p s hw hp table &&
    table.lookup? (discSlack sourceSquare v) == some 1

theorem checkDisc_sound {p : ZPoly} {s : DyadicSquare}
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table
      (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (sourceSquare : DyadicSquare)
    (v : PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (accepted : checkDisc hw hp table sourceSquare v = true) :
    ((Field.value (Field.literalRep p s hw hp) v : ℝ) : ℂ) ∈
      HexRootsMathlib.DyadicSquare.closedDisc sourceSquare := by
  have hparts : Field.checkSignTable p s hw hp table = true ∧
      table.lookup? (discSlack sourceSquare v) = some 1 := by
    simpa only [checkDisc, Bool.and_eq_true, beq_iff_eq] using accepted
  have hs := Field.checkSignTable_lookup p s hw hp table hparts.1
    (discSlack sourceSquare v) 1 hparts.2
  have hsign : SignType.sign
      (Field.value (Field.literalRep p s hw hp) (discSlack sourceSquare v)) = 1 := by
    cases h : SignType.sign
      (Field.value (Field.literalRep p s hw hp) (discSlack sourceSquare v)) with
    | zero => simp [h] at hs
    | neg => simp [h] at hs
    | pos => rfl
  have hpos := sign_eq_one_iff.mp hsign
  have hreal : s.meetsRealAxis = true := by
    have h := hparts.1
    simp only [Field.checkSignTable, Bool.and_eq_true] at h
    exact h.1.2
  rw [discSlack_value hw hp hreal sourceSquare v] at hpos
  exact in_disc_of_slack sourceSquare _ hpos

/-- A real root of the source polynomial inside the source's certified disc
is the exact selected real algebraic value. -/
theorem source_value (a : RealAlgebraicNumber) (x : ℝ)
    (hroot : (HexRootsMathlib.toPolyℂ a.toAlgebraic.p).IsRoot (x : ℂ))
    (hdisc : (x : ℂ) ∈
      HexRootsMathlib.DyadicSquare.closedDisc a.toAlgebraic.rep.1.square) :
    x = a.toReal := by
  apply Complex.ofReal_injective
  calc
    (x : ℂ) = HexRootsMathlib.RefinedIsolation.root a.toAlgebraic.rep :=
      HexRootsMathlib.RefinedIsolation.eq_root_of_mem_closedDisc
        a.toAlgebraic.rep hroot hdisc
    _ = a.toAlgebraic.toComplex := rfl
    _ = (a.toReal : ℂ) := (RealAlgebraicNumber.ofReal_toReal a).symm

/-- A finite equation check and a sign-table enclosure check together bind
one coordinate to one source value. -/
@[expose] def checkEntry {p : ZPoly} {s : DyadicSquare}
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table
      (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (sourcePolynomial : DensePoly Rat) (sourceSquare : DyadicSquare)
    (v : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) : Bool :=
  checkEquation sourcePolynomial v && checkDisc hw hp table sourceSquare v

theorem checkEntry_sound {p : ZPoly} {s : DyadicSquare}
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table
      (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (source : RealAlgebraicNumber) (sourcePolynomial : DensePoly Rat)
    (sourceSquare : DyadicSquare)
    (hpolynomial : ZPoly.toRatPoly source.toAlgebraic.p = sourcePolynomial)
    (hsource : source.toAlgebraic.rep.1.square = sourceSquare)
    (v : PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (accepted : checkEntry hw hp table sourcePolynomial sourceSquare v = true) :
    Field.value (Field.literalRep p s hw hp) v = source.toReal := by
  have hparts : checkEquation sourcePolynomial v = true ∧
      checkDisc hw hp table sourceSquare v = true := by
    simpa only [checkEntry, Bool.and_eq_true] using accepted
  have hreal : s.meetsRealAxis = true := by
    have h := hparts.2
    simp only [checkDisc, Bool.and_eq_true, Field.checkSignTable] at h
    exact h.1.1.2
  have hdisc : ((Field.value (Field.literalRep p s hw hp) v : ℝ) : ℂ) ∈
      HexRootsMathlib.DyadicSquare.closedDisc source.toAlgebraic.rep.1.square := by
    rw [hsource]
    exact checkDisc_sound hw hp table sourceSquare v hparts.2
  exact source_value source _
    (realPoly_root_complex source.toAlgebraic.p _ (by
      rw [hpolynomial]
      exact checkEquation_sound hw hp hreal sourcePolynomial v hparts.1)) hdisc

/-- A source whose selected real value has already been proved mathematically
can use the same finite replay without reducing its canonical construction. -/
theorem checkEntry_sound_of_selected {p : ZPoly} {s : DyadicSquare}
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table
      (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (sourcePolynomial : DensePoly Rat) (sourceSquare : DyadicSquare)
    (sourceP : ZPoly)
    (hwSource : atomWitness sourceP sourceSquare)
    (hpSource : (mahlerPrec sourceP : Int) ≤ sourceSquare.prec)
    (hpolynomial : sourcePolynomial = ZPoly.toRatPoly sourceP)
    (sourceValue : ℝ)
    (hselected : (Field.literalRep sourceP sourceSquare hwSource hpSource).root.re =
      sourceValue)
    (v : PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (accepted : checkEntry hw hp table sourcePolynomial sourceSquare v = true) :
    Field.value (Field.literalRep p s hw hp) v = sourceValue := by
  have hparts : checkEquation sourcePolynomial v = true ∧
      checkDisc hw hp table sourceSquare v = true := by
    simpa only [checkEntry, Bool.and_eq_true] using accepted
  have hreal : s.meetsRealAxis = true := by
    have h := hparts.2
    simp only [checkDisc, Bool.and_eq_true, Field.checkSignTable] at h
    exact h.1.1.2
  have hroot : (HexRootsMathlib.toPolyℂ sourceP).IsRoot
      ((Field.value (Field.literalRep p s hw hp) v : ℝ) : ℂ) := by
    apply realPoly_root_complex sourceP
    rw [← hpolynomial]
    exact checkEquation_sound hw hp hreal sourcePolynomial v hparts.1
  have hdisc : ((Field.value (Field.literalRep p s hw hp) v : ℝ) : ℂ) ∈
      HexRootsMathlib.DyadicSquare.closedDisc
        (Field.literalRep sourceP sourceSquare hwSource hpSource).1.square := by
    simpa only [Field.literalRep_square] using
      (checkDisc_sound hw hp table sourceSquare v hparts.2)
  have hsame := HexRootsMathlib.RefinedIsolation.eq_root_of_mem_closedDisc
    (Field.literalRep sourceP sourceSquare hwSource hpSource) hroot hdisc
  have hre := congrArg Complex.re hsame
  simpa only [Complex.ofReal_re, hselected] using hre

/-- Check each source against its corresponding coordinate in the original
order, including duplicates. The common root and its selected square are
shared by all entries. -/
@[expose] def checkPresentation {p : ZPoly} {s : DyadicSquare}
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table
      (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    {n : Nat} (sourcePolynomials : Fin n → DensePoly Rat)
    (sourceSquares : Fin n → DyadicSquare)
    (coordinates : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp)) : Bool :=
  Field.checkSignTable p s hw hp table &&
    (List.finRange n).all fun i =>
      checkEquation (sourcePolynomials i) (coordinates i) &&
        table.lookup? (discSlack (sourceSquares i) (coordinates i)) == some 1

/-- A successful finite replay gives the exact ordered source valuation,
including the empty collection. -/
theorem checkPresentation_sound {p : ZPoly} {s : DyadicSquare}
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table
      (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    {n : Nat} (sources : Fin n → RealAlgebraicNumber)
    (sourcePolynomials : Fin n → DensePoly Rat)
    (sourceSquares : Fin n → DyadicSquare)
    (coordinates : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (hpolynomial : ∀ i, ZPoly.toRatPoly (sources i).toAlgebraic.p = sourcePolynomials i)
    (hsource : ∀ i, (sources i).toAlgebraic.rep.1.square = sourceSquares i)
    (accepted : checkPresentation hw hp table sourcePolynomials sourceSquares coordinates = true) :
    (fun i => Field.value (Field.literalRep p s hw hp) (coordinates i)) =
      (fun i => (sources i).toReal) := by
  funext i
  have hparts : Field.checkSignTable p s hw hp table = true ∧
      (List.finRange n).all (fun j =>
        checkEquation (sourcePolynomials j) (coordinates j) &&
          table.lookup? (discSlack (sourceSquares j) (coordinates j)) == some 1) = true := by
    simpa only [checkPresentation, Bool.and_eq_true] using accepted
  have hrow := List.all_eq_true.mp hparts.2 i (List.mem_finRange i)
  have hentry : checkEntry hw hp table (sourcePolynomials i)
      (sourceSquares i) (coordinates i) = true := by
    simp only [checkEntry, checkDisc, Bool.and_eq_true, beq_iff_eq] at hrow ⊢
    exact ⟨hrow.1, hparts.1, hrow.2⟩
  exact checkEntry_sound hw hp table (sources i) (sourcePolynomials i)
    (sourceSquares i) (hpolynomial i) (hsource i) (coordinates i) hentry

end Hex.RCF.RealCoefficients.CommonPresentation
