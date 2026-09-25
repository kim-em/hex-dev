/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Field
public import HexRealFormulaMathlib.Semantics

public section

/-! A checked square-root alias for the small user-facing demonstration. -/

namespace Hex.RCF.RealCoefficients.SquareTwo

open Hex

abbrev polynomial : ZPoly := DensePoly.ofList [-2, 0, 1]

abbrev coordinate (s : DyadicSquare)
    (hw : atomWitness polynomial s)
    (hp : (mahlerPrec polynomial : Int) ≤ s.prec) :
    PolyQuot polynomial (SimpleRoot.ofSquare polynomial s hw hp) :=
  PolyQuot.ofSquare polynomial s (DensePoly.ofList [0, 1]) hw hp

theorem value (s : DyadicSquare)
    (hw : atomWitness polynomial s)
    (hp : (mahlerPrec polynomial : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true)
    (hpositive : 0 < ((s.re - s.radiusHi).toRat : ℝ)) :
    Field.value (Field.literalRep polynomial s hw hp) (coordinate s hw hp) =
      Real.sqrt 2 := by
  let rep := Field.literalRep polynomial s hw hp
  let v := coordinate s hw hp
  have hv : v.coeffs = DensePoly.monomial 1 (1 : Rat) := by
    dsimp [v, coordinate, PolyQuot.ofSquare, PolyQuot.reduce, PolyQuot.reduceCoeffs]
    rw [DensePoly.mod_eq_self_of_degree_lt _ _ (by decide)]
    rfl
  have hval : Field.value rep v = rep.root.re := by
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
  have hroot := Field.literalRep_root polynomial s hw hp hreal
  have hsq : rep.root.re ^ 2 = 2 := by
    have hpoly : LiteralSign.realPoly (ZPoly.toRatPoly polynomial) =
        Polynomial.X ^ 2 - Polynomial.C 2 := by
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
      have h3 : 3 ≤ i := by omega
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (show [(-2 : Int), 0, 1].length ≤ i by simp; omega)]
      simp only [Option.getD_none, if_neg h0, if_neg h2]
      norm_num
    rw [hpoly] at hroot
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at hroot
    nlinarith
  have hpos : 0 ≤ rep.root.re :=
    le_of_lt (hpositive.trans (Field.literalRep_bounds polynomial s hw hp).1)
  rw [hval]
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsqrt_nonneg := Real.sqrt_nonneg 2
  nlinarith

/-- A one-coordinate formula sees the literal field root as the user's
square-root coefficient. -/
theorem valuation (s : DyadicSquare)
    (hw : atomWitness polynomial s)
    (hp : (mahlerPrec polynomial : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true)
    (hpositive : 0 < ((s.re - s.radiusHi).toRat : ℝ))
    (values : Fin 1 → PolyQuot polynomial (SimpleRoot.ofSquare polynomial s hw hp))
    (hvalue : values 0 = coordinate s hw hp) :
    (fun i => Field.value (Field.literalRep polynomial s hw hp) (values i)) =
      Hex.RealFormula.append Fin.elim0 (Real.sqrt 2) := by
  funext i
  fin_cases i
  simpa [hvalue, Hex.RealFormula.append] using value s hw hp hreal hpositive

abbrev square : DyadicSquare :=
  ⟨Dyadic.ofInt 181 >>> (7 : Int), 0, 8⟩

theorem checked : polynomial.CheckedIrreducible :=
  Field.checkedIrreducible polynomial (.eisenstein 2 0) (by decide +kernel) (by decide)

theorem squarefree : HasOnlySimpleRoots polynomial := by
  have hne : polynomial ≠ 0 := by decide
  letI : polynomial.CheckedIrreducible := checked
  exact (HexRootsMathlib.hasOnlySimpleRoots_iff_separable polynomial hne).mpr
    (ZPoly.CheckedIrreducible.separable polynomial)

end Hex.RCF.RealCoefficients.SquareTwo
