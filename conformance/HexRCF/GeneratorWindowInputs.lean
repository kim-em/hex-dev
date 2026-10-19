/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
@[expose] public section

namespace Hex.RCF.GeneratorWindowTests
open Hex RealCoefficients LiteralSign

instance : SquareTwo.polynomial.CheckedIrreducible := SquareTwo.checked
abbrev hw : atomWitness SquareTwo.polynomial SquareTwo.square := by decide
abbrev hp : (mahlerPrec SquareTwo.polynomial : Int) ≤ SquareTwo.square.prec := by decide
abbrev root := SimpleRoot.ofSquare SquareTwo.polynomial SquareTwo.square hw hp
theorem real : SquareTwo.square.meetsRealAxis = true := by decide
abbrev K := PolyQuot SquareTwo.polynomial root
def theta : K := SquareTwo.coordinate SquareTwo.square hw hp
def close : K :=
  PolyQuot.ofSquare SquareTwo.polynomial SquareTwo.square
    (DensePoly.C (181 / 128 : Rat)) hw hp - theta
def table? (keys : List K) : Option (Table K) :=
  Table.build (ZPoly.toRatPoly SquareTwo.polynomial)
    (SquareTwo.square.re - SquareTwo.square.radiusHi).toRat
    (SquareTwo.square.re + SquareTwo.square.radiusHi).toRat keys PolyQuot.coeffs

def values : Fin 1 → K := fun _ => theta
def matrix : RealFormula.QF 2 :=
  .and (.atom ⟨MvPoly.X 1 ^ 2 - MvPoly.X 0, .eq⟩)
    (.and (.atom ⟨1 - MvPoly.X 1, .lt⟩) (.atom ⟨MvPoly.X 1 - 2, .lt⟩))

end Hex.RCF.GeneratorWindowTests
