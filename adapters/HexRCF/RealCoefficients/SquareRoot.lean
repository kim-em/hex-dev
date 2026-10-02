/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Field

public section

namespace Hex.RCF.RealCoefficients.SquareRoot

/-- The defining polynomial of a natural-number square root. -/
@[expose] def polynomial (n : Nat) : ZPoly :=
  DensePoly.ofList [-(n : Int), 0, 1]

/-- A positive selected root of `X² - n` is the user's `Real.sqrt n`.
The proof uses only the literal polynomial and isolating square. -/
theorem selected (n : Nat) (s : DyadicSquare)
    (hw : atomWitness (polynomial n) s)
    (hp : (mahlerPrec (polynomial n) : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true)
    (hpositive : 0 < ((s.re - s.radiusHi).toRat : ℝ)) :
    (Field.literalRep (polynomial n) s hw hp).root.re = Real.sqrt n := by
  let rep := Field.literalRep (polynomial n) s hw hp
  have hroot := Field.literalRep_root (polynomial n) s hw hp hreal
  have hpoly : LiteralSign.realPoly (ZPoly.toRatPoly (polynomial n)) =
      (Polynomial.X : Polynomial ℝ) ^ 2 - Polynomial.C (n : ℝ) := by
    ext i
    simp [LiteralSign.realPoly, polynomial, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow]
    by_cases hi : i < 3
    · interval_cases i <;> norm_num at *
    · have hne0 : i ≠ 0 := by omega
      have hne2 : i ≠ 2 := by omega
      simp [hi, hne0, hne2]
      rfl
  rw [hpoly] at hroot
  have hsquare : rep.root.re ^ 2 = n := by
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at hroot
    linarith
  have hpos : 0 < rep.root.re := hpositive.trans
    (Field.literalRep_bounds (polynomial n) s hw hp).1
  have hsqrt : (Real.sqrt n) ^ 2 = n := by
    rw [Real.sq_sqrt]
    exact_mod_cast Nat.zero_le n
  have hsqrt_nonneg := Real.sqrt_nonneg (n : ℝ)
  nlinarith

end Hex.RCF.RealCoefficients.SquareRoot
