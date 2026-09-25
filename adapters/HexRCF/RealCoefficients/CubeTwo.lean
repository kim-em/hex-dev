/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Selected
public import HexRealFormulaMathlib.Semantics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

/-! The selected cubic root denotes Mathlib's real power notation. -/

namespace Hex.RCF.RealCoefficients.CubeTwo

open Hex

abbrev polynomial : ZPoly := DensePoly.ofList [-2, 0, 0, 1]

abbrev coordinate (s : DyadicSquare)
    (hw : atomWitness polynomial s)
    (hp : (mahlerPrec polynomial : Int) ≤ s.prec) :
    PolyQuot polynomial (SimpleRoot.ofSquare polynomial s hw hp) :=
  PolyQuot.ofSquare polynomial s (DensePoly.ofList [0, 1]) hw hp

theorem coordinate_value (s : DyadicSquare)
    (hw : atomWitness polynomial s)
    (hp : (mahlerPrec polynomial : Int) ≤ s.prec) :
    Field.value (Field.literalRep polynomial s hw hp) (coordinate s hw hp) =
      (Field.literalRep polynomial s hw hp).root.re := by
  let rep := Field.literalRep polynomial s hw hp
  let v := coordinate s hw hp
  have hv : v.coeffs = DensePoly.monomial 1 (1 : Rat) := by
    dsimp [v, coordinate, PolyQuot.ofSquare, PolyQuot.reduce, PolyQuot.reduceCoeffs]
    rw [DensePoly.mod_eq_self_of_degree_lt _ _ (by decide)]
    rfl
  rw [Field.value_realPoly rep v, hv]
  have hpoly : LiteralSign.realPoly (DensePoly.monomial 1 (1 : Rat)) =
      Polynomial.X := by
    ext i
    simp only [LiteralSign.realPoly, HexPolyMathlib.Interpret.coeff_interpret,
      DensePoly.coeff_monomial, Polynomial.coeff_X]
    by_cases hi : i = 1
    · subst i; norm_num
    · have hi' : 1 ≠ i := Ne.symm hi
      simp only [if_neg hi, if_neg hi']
      norm_num
  rw [hpoly, Polynomial.eval_X]

theorem value (s : DyadicSquare)
    (hw : atomWitness polynomial s)
    (hp : (mahlerPrec polynomial : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true) :
    Field.value (Field.literalRep polynomial s hw hp) (coordinate s hw hp) =
      (2 : ℝ) ^ (1 / 3 : ℝ) := by
  let rep := Field.literalRep polynomial s hw hp
  have hval := coordinate_value s hw hp
  have hroot := Field.literalRep_root polynomial s hw hp hreal
  have hcubed : rep.root.re ^ 3 = 2 := by
    have hpoly : LiteralSign.realPoly (ZPoly.toRatPoly polynomial) =
        Polynomial.X ^ 3 - Polynomial.C 2 := by
      ext i
      simp only [LiteralSign.realPoly, HexPolyMathlib.Interpret.coeff_interpret,
        ZPoly.coeff_toRatPoly, polynomial, DensePoly.coeff_ofList,
        Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      by_cases h0 : i = 0
      · subst i; norm_num
      by_cases h1 : i = 1
      · subst i; norm_num
      by_cases h2 : i = 2
      · subst i; norm_num
      by_cases h3 : i = 3
      · subst i; norm_num
      have h4 : 4 ≤ i := by omega
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (show [(-2 : Int), 0, 0, 1].length ≤ i by simp; omega)]
      simp only [Option.getD_none, if_neg h0, if_neg h3]
      norm_num
    rw [hpoly] at hroot
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at hroot
    nlinarith
  have hpower : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
    simpa only [one_div, Nat.cast_ofNat] using
      (Real.rpow_inv_natCast_pow (x := (2 : ℝ)) (n := 3)
        (by norm_num) (by decide))
  rw [hval]
  exact (show Odd 3 by decide).pow_injective (hcubed.trans hpower.symm)

theorem valuation (s : DyadicSquare)
    (hw : atomWitness polynomial s)
    (hp : (mahlerPrec polynomial : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true)
    (values : Fin 1 → PolyQuot polynomial (SimpleRoot.ofSquare polynomial s hw hp))
    (hvalue : values 0 = coordinate s hw hp) :
    (fun i => Field.value (Field.literalRep polynomial s hw hp) (values i)) =
      Hex.RealFormula.append Fin.elim0 ((2 : ℝ) ^ (1 / 3 : ℝ)) := by
  funext i
  fin_cases i
  simpa [hvalue, Hex.RealFormula.append] using value s hw hp hreal

/-- A compact, checked presentation of the positive cubic root as Hex's
canonical real algebraic number. -/
abbrev square : DyadicSquare :=
  ⟨Dyadic.ofInt 1290 >>> (10 : Int), 0, 12⟩

private theorem checked : polynomial.CheckedIrreducible :=
  Field.checkedIrreducible polynomial (.eisenstein 2 0) (by decide +kernel) (by decide)

private theorem squarefree : HasOnlySimpleRoots polynomial := by
  have hne : polynomial ≠ 0 := by decide
  letI : polynomial.CheckedIrreducible := checked
  exact (HexRootsMathlib.hasOnlySimpleRoots_iff_separable polynomial hne).mpr
    (ZPoly.CheckedIrreducible.separable polynomial)

def realAlgebraic : RealAlgebraicNumber :=
  Selected.real polynomial square (by decide) (by decide)
    (by rfl) (by decide) (by decide) checked squarefree (by decide)

theorem realAlgebraic_toReal :
    realAlgebraic.toReal = (2 : ℝ) ^ (1 / 3 : ℝ) := by
  have hroot := Selected.real_toReal polynomial square (by decide) (by decide)
    (by rfl) (by decide) (by decide) checked squarefree (by decide)
  change realAlgebraic.toReal = _ at hroot
  rw [hroot]
  rw [← coordinate_value square (by decide) (by decide)]
  exact value square (by decide) (by decide) (by decide)

theorem valuationAlgebraic (s : DyadicSquare)
    (hw : atomWitness polynomial s)
    (hp : (mahlerPrec polynomial : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true)
    (values : Fin 1 → PolyQuot polynomial (SimpleRoot.ofSquare polynomial s hw hp))
    (hvalue : values 0 = coordinate s hw hp) :
    (fun i => Field.value (Field.literalRep polynomial s hw hp) (values i)) =
      Hex.RealFormula.append Fin.elim0 realAlgebraic.toReal := by
  rw [realAlgebraic_toReal]
  exact valuation s hw hp hreal values hvalue

/-- A coefficient obtained by ordinary arithmetic in Hex's fixed number
field, then converted back to the real algebraic API. -/
abbrev shifted : RealAlgebraicNumber :=
  Coefficients.ofField realAlgebraic
    (1 + realAlgebraic.toAlgebraic.toQAdjoin)

theorem shifted_toReal : shifted.toReal = 1 + realAlgebraic.toReal := by
  let a := realAlgebraic
  have hreal : a.toAlgebraic.rep.root.im = 0 :=
    (AlgebraicNumber.isReal_iff a.toAlgebraic).mp a.property
  rw [shifted, Field.ofField_value,
    Field.value_add a.toAlgebraic.rep a.toAlgebraic.rep_mk hreal,
    Field.value_one a.toAlgebraic.rep a.toAlgebraic.rep_mk hreal,
    Field.generator_value]

abbrev shiftedCoordinate (s : DyadicSquare)
    (hw : atomWitness polynomial s)
    (hp : (mahlerPrec polynomial : Int) ≤ s.prec) :
    PolyQuot polynomial (SimpleRoot.ofSquare polynomial s hw hp) :=
  1 + coordinate s hw hp

theorem shifted_value (s : DyadicSquare)
    (hw : atomWitness polynomial s)
    (hp : (mahlerPrec polynomial : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true) :
    Field.value (Field.literalRep polynomial s hw hp)
        (shiftedCoordinate s hw hp) = shifted.toReal := by
  letI : polynomial.CheckedIrreducible := checked
  have hrep := Field.literalRep_mk polynomial s hw hp
  have hroot := Field.literalRep_real polynomial s hw hp hreal
  rw [Field.value_add (Field.literalRep polynomial s hw hp) hrep hroot,
    Field.value_one (Field.literalRep polynomial s hw hp) hrep hroot,
    value s hw hp hreal, shifted_toReal, realAlgebraic_toReal]

theorem valuationShifted (s : DyadicSquare)
    (hw : atomWitness polynomial s)
    (hp : (mahlerPrec polynomial : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true)
    (values : Fin 1 → PolyQuot polynomial (SimpleRoot.ofSquare polynomial s hw hp))
    (hvalue : values 0 = shiftedCoordinate s hw hp) :
    (fun i => Field.value (Field.literalRep polynomial s hw hp) (values i)) =
      Hex.RealFormula.append Fin.elim0 shifted.toReal := by
  funext i
  fin_cases i
  simpa [hvalue, Hex.RealFormula.append] using shifted_value s hw hp hreal

end Hex.RCF.RealCoefficients.CubeTwo
