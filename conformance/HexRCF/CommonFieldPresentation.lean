/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Field
public import HexRCF.RealCoefficients.RootAliases

public section

/-!
An explicit common field for two independently constructed real radicals.
The field data are finite: a polynomial, an isolating square, and two rational
coordinate polynomials. These proofs validate their real values without
reducing the primitive-element search. The Hex source radicals are identified
through their proved positive-square-root formulas; this is a concrete case,
not a general source-comparison checker.
-/

namespace Hex.RCF.CommonFieldPresentation

open Hex.RCF.RealCoefficients

/-- Polynomial identities give the squares of both proposed coordinates.
They do not determine the signs of those coordinates. -/
theorem coordinate_squares (r : ℝ)
    (hpoly : r ^ 4 - 10 * r ^ 2 + 1 = 0) :
    ((11 * r - r ^ 3) / 2) ^ 2 = 3 ∧
      ((r ^ 3 - 9 * r) / 2) ^ 2 = 2 := by
  constructor
  · nlinarith [show 4 * (((11 * r - r ^ 3) / 2) ^ 2 - 3) =
      (r ^ 2 - 12) * (r ^ 4 - 10 * r ^ 2 + 1) by ring]
  · nlinarith [show 4 * (((r ^ 3 - 9 * r) / 2) ^ 2 - 2) =
      (r ^ 2 - 8) * (r ^ 4 - 10 * r ^ 2 + 1) by ring]

/-- The two proposed coordinates can be checked from a polynomial equation
and a small rational interval; the primitive-element search is not replayed. -/
theorem coordinates (r : ℝ)
    (hpoly : r ^ 4 - 10 * r ^ 2 + 1 = 0)
    (hlo : 3 < r) (hhi : r < (16 : ℝ) / 5) :
    (11 * r - r ^ 3) / 2 = Real.sqrt 3 ∧
      (r ^ 3 - 9 * r) / 2 = Real.sqrt 2 := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have h2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have h3nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have h2nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hrpos : 0 < r := by linarith
  have hr2lower : 9 < r ^ 2 := by nlinarith
  have hr2upper : r ^ 2 < 11 := by nlinarith
  have hu_pos : 0 < (11 * r - r ^ 3) / 2 := by nlinarith [mul_pos hrpos (sub_pos.mpr hr2upper)]
  have hv_pos : 0 < (r ^ 3 - 9 * r) / 2 := by nlinarith [mul_pos hrpos (sub_pos.mpr hr2lower)]
  obtain ⟨hu2, hv2⟩ := coordinate_squares r hpoly
  constructor <;> nlinarith

/-- A different positive root of the same polynomial changes the second
coordinate to the negative square root. -/
theorem small_coordinates (r : ℝ)
    (hpoly : r ^ 4 - 10 * r ^ 2 + 1 = 0)
    (hlo : 0 < r) (hhi : r < 1) :
    (11 * r - r ^ 3) / 2 = Real.sqrt 3 ∧
      (r ^ 3 - 9 * r) / 2 = -Real.sqrt 2 := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have h2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have h3nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have h2nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2upper : r ^ 2 < 1 := by nlinarith
  have hu_pos : 0 < (11 * r - r ^ 3) / 2 := by
    nlinarith [mul_pos hlo (show 0 < 11 - r ^ 2 by linarith)]
  have hv_neg : (r ^ 3 - 9 * r) / 2 < 0 := by
    nlinarith [mul_pos hlo (show 0 < 9 - r ^ 2 by linarith)]
  obtain ⟨hu2, hv2⟩ := coordinate_squares r hpoly
  constructor <;> nlinarith

/-- The proposed defining polynomial for `√3 + √2`. -/
def quartic : ZPoly := DensePoly.ofList [1, 0, -10, 0, 1]

/-- The selected real part satisfies the literal quartic. -/
theorem root_equation (s : DyadicSquare)
    (hw : atomWitness quartic s)
    (hp : (mahlerPrec quartic : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true) :
    (Field.literalRep quartic s hw hp).root.re ^ 4 -
      10 * (Field.literalRep quartic s hw hp).root.re ^ 2 + 1 = 0 := by
  have hroot := Field.literalRep_root quartic s hw hp hreal
  have hpolyeq : LiteralSign.realPoly (ZPoly.toRatPoly quartic) =
      (Polynomial.X : Polynomial ℝ) ^ 4 -
        Polynomial.C 10 * Polynomial.X ^ 2 + Polynomial.C 1 := by
    ext n
    simp [LiteralSign.realPoly, quartic, Polynomial.coeff_sub,
      Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_one]
    by_cases hn : n < 5
    · interval_cases n <;> norm_num at *
    · have hn' : 5 ≤ n := by omega
      have hn0 : n ≠ 0 := by omega
      have hn2 : n ≠ 2 := by omega
      have hn4 : n ≠ 4 := by omega
      simp [hn', hn0, hn2, hn4]; rfl
  rw [hpolyeq] at hroot
  simpa [Polynomial.IsRoot] using hroot

theorem selected_coordinates (s : DyadicSquare)
    (hw : atomWitness quartic s)
    (hp : (mahlerPrec quartic : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true)
    (hlo : (3 : ℝ) < ((s.re - s.radiusHi).toRat : ℝ))
    (hhi : (((s.re + s.radiusHi).toRat : Rat) : ℝ) < (16 : ℝ) / 5) :
    let r := (Field.literalRep quartic s hw hp).root.re
    (11 * r - r ^ 3) / 2 = Real.sqrt 3 ∧
      (r ^ 3 - 9 * r) / 2 = Real.sqrt 2 := by
  have hpoly := root_equation s hw hp hreal
  have hb := Field.literalRep_bounds quartic s hw hp
  exact coordinates _ hpoly (lt_trans hlo hb.1) (lt_trans hb.2 hhi)

/-- A checked real isolating square for the intended root of `quartic`. -/
def square : DyadicSquare :=
  ⟨(Dyadic.ofInt 6918708517617) >>> (41 : Int), 0, 37⟩

theorem squareWitness : atomWitness quartic square := by decide +kernel

theorem squarePrecision : (mahlerPrec quartic : Int) ≤ square.prec := by decide +kernel

theorem squareReal : square.meetsRealAxis = true := by decide +kernel

theorem square_re :
    square.re.toRat = (6918708517617 : Rat) / 2199023255552 := by
  decide_cbv

theorem square_radius :
    square.radiusHi.toRat = (1449 : Rat) / 140737488355328 := by
  decide_cbv

theorem square_coordinates :
    let r := (Field.literalRep quartic square squareWitness squarePrecision).root.re
    (11 * r - r ^ 3) / 2 = Real.sqrt 3 ∧
      (r ^ 3 - 9 * r) / 2 = Real.sqrt 2 := by
  apply selected_coordinates square squareWitness squarePrecision squareReal
  · norm_num [Dyadic.toRat_sub, square_re, square_radius]
  · norm_num [Dyadic.toRat_add, square_re, square_radius]

def coord3 (s : DyadicSquare)
    (hw : atomWitness quartic s)
    (hp : (mahlerPrec quartic : Int) ≤ s.prec) :
    PolyQuot quartic (SimpleRoot.ofSquare quartic s hw hp) :=
  PolyQuot.ofSquare quartic s (DensePoly.ofList [0, (11 : Rat) / 2, 0, -1 / 2]) hw hp

def coord2 (s : DyadicSquare)
    (hw : atomWitness quartic s)
    (hp : (mahlerPrec quartic : Int) ≤ s.prec) :
    PolyQuot quartic (SimpleRoot.ofSquare quartic s hw hp) :=
  PolyQuot.ofSquare quartic s (DensePoly.ofList [0, (-9 : Rat) / 2, 0, 1 / 2]) hw hp

theorem coord3_coeffs (s : DyadicSquare)
    (hw : atomWitness quartic s)
    (hp : (mahlerPrec quartic : Int) ≤ s.prec) :
    (coord3 s hw hp).coeffs =
      DensePoly.ofList [0, (11 : Rat) / 2, 0, -1 / 2] := by
  decide_cbv

theorem coord2_coeffs (s : DyadicSquare)
    (hw : atomWitness quartic s)
    (hp : (mahlerPrec quartic : Int) ≤ s.prec) :
    (coord2 s hw hp).coeffs =
      DensePoly.ofList [0, (-9 : Rat) / 2, 0, 1 / 2] := by
  decide_cbv

theorem coord3_value (s : DyadicSquare)
    (hw : atomWitness quartic s)
    (hp : (mahlerPrec quartic : Int) ≤ s.prec) :
    Field.value (Field.literalRep quartic s hw hp) (coord3 s hw hp) =
      (11 * (Field.literalRep quartic s hw hp).root.re -
        (Field.literalRep quartic s hw hp).root.re ^ 3) / 2 := by
  rw [Field.value_realPoly, coord3_coeffs]
  have hpoly : LiteralSign.realPoly
      (DensePoly.ofList [0, (11 : Rat) / 2, 0, -1 / 2]) =
      Polynomial.C (11 / 2 : ℝ) * Polynomial.X -
        Polynomial.C (1 / 2 : ℝ) * Polynomial.X ^ 3 := by
    ext n
    simp [LiteralSign.realPoly, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X]
    by_cases hn : n < 4
    · interval_cases n <;> norm_num at *
    · have hn' : 4 ≤ n := by omega
      have hn3 : n ≠ 3 := by omega
      have h1n : 1 ≠ n := by omega
      simp [hn', h1n, hn3]; rfl
  rw [hpoly]
  simp [Polynomial.eval_sub, Polynomial.eval_mul]
  ring

theorem coord2_value (s : DyadicSquare)
    (hw : atomWitness quartic s)
    (hp : (mahlerPrec quartic : Int) ≤ s.prec) :
    Field.value (Field.literalRep quartic s hw hp) (coord2 s hw hp) =
      ((Field.literalRep quartic s hw hp).root.re ^ 3 -
        9 * (Field.literalRep quartic s hw hp).root.re) / 2 := by
  rw [Field.value_realPoly, coord2_coeffs]
  have hpoly : LiteralSign.realPoly
      (DensePoly.ofList [0, (-9 : Rat) / 2, 0, 1 / 2]) =
      Polynomial.C (-9 / 2 : ℝ) * Polynomial.X +
        Polynomial.C (1 / 2 : ℝ) * Polynomial.X ^ 3 := by
    ext n
    simp [LiteralSign.realPoly, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X]
    by_cases hn : n < 4
    · interval_cases n <;> norm_num at *
    · have hn' : 4 ≤ n := by omega
      have h1n : 1 ≠ n := by omega
      have hn3 : n ≠ 3 := by omega
      simp [hn', h1n, hn3]; rfl
  rw [hpoly]
  simp [Polynomial.eval_add, Polynomial.eval_mul]
  ring

theorem square_values :
    let rep := Field.literalRep quartic square squareWitness squarePrecision
    Field.value rep (coord3 square squareWitness squarePrecision) = Real.sqrt 3 ∧
      Field.value rep (coord2 square squareWitness squarePrecision) = Real.sqrt 2 := by
  obtain ⟨h3, h2⟩ := square_coordinates
  dsimp only
  rw [coord3_value, coord2_value]
  exact ⟨h3, h2⟩

/-- The rational input to the first Hex radical is nonnegative. -/
theorem threeNonneg : 0 ≤ RealAlgebraicNumber.ofRat 3 := by
  rw [RealAlgebraicNumber.le_iff, RealAlgebraicNumber.zero_toReal,
    RealAlgebraicNumber.ofRat_toReal]
  norm_num

/-- The rational input to the second Hex radical is nonnegative. -/
theorem twoNonneg : 0 ≤ RealAlgebraicNumber.ofRat 2 := by
  rw [RealAlgebraicNumber.le_iff, RealAlgebraicNumber.zero_toReal,
    RealAlgebraicNumber.ofRat_toReal]
  norm_num

/-- A Hex radical constructed independently of the common presentation. -/
def hexSqrt3 : RealAlgebraicNumber :=
  Coefficients.root (RealAlgebraicNumber.ofRat 3) 2 threeNonneg

/-- A second Hex radical constructed from a different rational input. -/
def hexSqrt2 : RealAlgebraicNumber :=
  Coefficients.root (RealAlgebraicNumber.ofRat 2) 2 twoNonneg

theorem hexSqrt3_value : hexSqrt3.toReal = Real.sqrt 3 := by
  simpa [hexSqrt3] using
    Coefficients.root_two (RealAlgebraicNumber.ofRat 3) threeNonneg

theorem hexSqrt2_value : hexSqrt2.toReal = Real.sqrt 2 := by
  simpa [hexSqrt2] using
    Coefficients.root_two (RealAlgebraicNumber.ofRat 2) twoNonneg

/-- The common coordinates denote these Hex sources, using their proved
positive-square-root formulas to identify the selected real values. -/
theorem source_values :
    let rep := Field.literalRep quartic square squareWitness squarePrecision
    Field.value rep (coord3 square squareWitness squarePrecision) = hexSqrt3.toReal ∧
      Field.value rep (coord2 square squareWitness squarePrecision) = hexSqrt2.toReal := by
  rw [hexSqrt3_value, hexSqrt2_value]
  exact square_values

/-- A second valid isolation of the same polynomial, near `√3 - √2`. -/
def smallSquare : DyadicSquare :=
  ⟨(Dyadic.ofInt 698931493666) >>> (41 : Int), 0, 37⟩

theorem smallWitness : atomWitness quartic smallSquare := by decide +kernel

theorem smallPrecision : (mahlerPrec quartic : Int) ≤ smallSquare.prec := by decide +kernel

theorem smallReal : smallSquare.meetsRealAxis = true := by decide +kernel

theorem small_re :
    smallSquare.re.toRat = (698931493666 : Rat) / 2199023255552 := by
  decide_cbv

theorem small_radius :
    smallSquare.radiusHi.toRat = (1449 : Rat) / 140737488355328 := by
  decide_cbv

theorem flipped_coordinates :
    let r := (Field.literalRep quartic smallSquare smallWitness smallPrecision).root.re
    (11 * r - r ^ 3) / 2 = Real.sqrt 3 ∧
      (r ^ 3 - 9 * r) / 2 = -Real.sqrt 2 := by
  have hb := Field.literalRep_bounds quartic smallSquare smallWitness smallPrecision
  have hlo : (0 : ℝ) < ((smallSquare.re - smallSquare.radiusHi).toRat : ℝ) := by
    norm_num [Dyadic.toRat_sub, small_re, small_radius]
  have hhi : (((smallSquare.re + smallSquare.radiusHi).toRat : Rat) : ℝ) < 1 := by
    norm_num [Dyadic.toRat_add, small_re, small_radius]
  exact small_coordinates _
    (root_equation smallSquare smallWitness smallPrecision smallReal)
    (hlo.trans hb.1) (hb.2.trans hhi)

/-- The same defining equation and coordinate polynomials now give the
negative square root of two. Root selection is indispensable. -/
theorem flipped_values :
    let rep := Field.literalRep quartic smallSquare smallWitness smallPrecision
    Field.value rep (coord3 smallSquare smallWitness smallPrecision) = Real.sqrt 3 ∧
      Field.value rep (coord2 smallSquare smallWitness smallPrecision) = -Real.sqrt 2 ∧
      Field.value rep (coord2 smallSquare smallWitness smallPrecision) ≠ Real.sqrt 2 := by
  obtain ⟨h3, h2⟩ := flipped_coordinates
  dsimp only
  rw [coord3_value, coord2_value]
  have hpos : 0 < Real.sqrt 2 := by positivity
  exact ⟨h3, h2, by rw [h2]; linarith⟩

/-- info: 'Hex.RCF.CommonFieldPresentation.square_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms square_values

/-- info: 'Hex.RCF.CommonFieldPresentation.source_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_values

/-- info: 'Hex.RCF.CommonFieldPresentation.flipped_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flipped_values

end Hex.RCF.CommonFieldPresentation
