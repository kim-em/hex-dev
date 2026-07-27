/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.Basic
public meta import HexNumberField.Basic

public section

/-!
Reduced arithmetic in a fixed rational polynomial presentation.

Every public operation returns the canonical remainder modulo the integer
defining polynomial cast to `Rat`. Inversion uses the left Bézout coefficient
from polynomial extended gcd and normalizes by its constant gcd.
-/
namespace Hex.QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

/-- Canonical rational-polynomial remainder modulo `p`. -/
@[expose]
def reduceCoeffs (p : ZPoly) (f : DensePoly Rat) : DensePoly Rat :=
  f % ZPoly.toRatPoly p

/-- Package a rational polynomial after canonical modular reduction. -/
@[expose]
def reduce (p : ZPoly) (x : SimpleRoot p) (f : DensePoly Rat) : QAdjoin p x where
  coeffs := reduceCoeffs p f
  degree_lt := by
    sorry

/-- Coordinate equality in a fixed presentation. -/
@[expose]
def beq (a b : QAdjoin p x) : Bool :=
  a.coeffs == b.coeffs

instance : BEq (QAdjoin p x) := ⟨beq⟩

/-- Boolean zero test on canonical coordinates. -/
@[expose]
def isZero (a : QAdjoin p x) : Bool :=
  a.coeffs.isZero

instance : Zero (QAdjoin p x) := ⟨reduce p x 0⟩

instance : One (QAdjoin p x) := ⟨reduce p x 1⟩

/-- Reduced coordinate addition. -/
@[expose]
def add (a b : QAdjoin p x) : QAdjoin p x :=
  reduce p x (a.coeffs + b.coeffs)

instance : Add (QAdjoin p x) := ⟨add⟩

/-- Reduced coordinate subtraction. -/
@[expose]
def sub (a b : QAdjoin p x) : QAdjoin p x :=
  reduce p x (a.coeffs - b.coeffs)

instance : Sub (QAdjoin p x) := ⟨sub⟩

/-- Reduced coordinate negation. -/
@[expose]
def neg (a : QAdjoin p x) : QAdjoin p x :=
  reduce p x (-a.coeffs)

instance : Neg (QAdjoin p x) := ⟨neg⟩

/-- Reduced coordinate multiplication. -/
@[expose]
def mul (a b : QAdjoin p x) : QAdjoin p x :=
  reduce p x (a.coeffs * b.coeffs)

instance : Mul (QAdjoin p x) := ⟨mul⟩

/-- Rational scalar action followed by canonical reduction. -/
@[expose]
def smul (c : Rat) (a : QAdjoin p x) : QAdjoin p x :=
  reduce p x (DensePoly.scale c a.coeffs)

instance : SMul Rat (QAdjoin p x) := ⟨smul⟩

/-- Extended-gcd inverse coordinates. Zero is fixed at zero; a successful
irreducible-field input has a nonzero constant gcd, whose inverse normalizes
the left Bézout coefficient. -/
@[expose]
def invCoeffs (p : ZPoly) (f : DensePoly Rat) : DensePoly Rat :=
  if f.isZero then
    0
  else
    let r := DensePoly.xgcd f (ZPoly.toRatPoly p)
    let c := r.gcd.leadingCoeff
    if c = 0 then
      0
    else
      reduceCoeffs p (DensePoly.scale c⁻¹ r.left)

/-- Inversion in a checked irreducible presentation, with `0⁻¹ = 0`. -/
@[expose]
def inv [ZPoly.CheckedIrreducible p] (a : QAdjoin p x) : QAdjoin p x :=
  reduce p x (invCoeffs p a.coeffs)

instance [ZPoly.CheckedIrreducible p] : Inv (QAdjoin p x) := ⟨inv⟩

/-- Division in a checked irreducible presentation. -/
@[expose]
def div [ZPoly.CheckedIrreducible p] (a b : QAdjoin p x) : QAdjoin p x :=
  a * b⁻¹

instance [ZPoly.CheckedIrreducible p] : Div (QAdjoin p x) := ⟨div⟩

/-! Compiled arithmetic regressions in `ℚ[X]/(X²-2)`. -/

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

#guard
    reduceCoeffs sqrtTwoPoly (DensePoly.ofList ([0, 0, 1] : List Rat)) =
      DensePoly.C 2

#guard
    let xPoly := DensePoly.ofList ([0, 1] : List Rat)
    reduceCoeffs sqrtTwoPoly (xPoly * xPoly) = DensePoly.C 2

#guard
    let xPoly := DensePoly.ofList ([0, 1] : List Rat)
    invCoeffs sqrtTwoPoly xPoly = DensePoly.ofList ([0, 1 / 2] : List Rat) &&
      reduceCoeffs sqrtTwoPoly (xPoly * invCoeffs sqrtTwoPoly xPoly) = 1

#guard invCoeffs sqrtTwoPoly 0 = 0

end Hex.QAdjoin
