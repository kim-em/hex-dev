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
  degree_lt := ZPoly.rat_mod_zpoly_degree_lt _ _ x.posDegree

/-- Fixed-presentation elements are equal when their canonical coordinates are
equal. -/
@[ext]
theorem ext {a b : QAdjoin p x} (h : a.coeffs = b.coeffs) : a = b := by
  cases a with
  | mk ac ah =>
      cases b with
      | mk bc bh =>
          change ac = bc at h
          subst bc
          rfl

/-- Equality is exactly equality of canonical coordinate polynomials. -/
theorem eq_iff_coeffs {a b : QAdjoin p x} : a = b ↔ a.coeffs = b.coeffs :=
  ⟨fun h => congrArg QAdjoin.coeffs h, ext⟩

instance : DecidableEq (QAdjoin p x) := by
  intro a b
  if h : a.coeffs = b.coeffs then
    exact isTrue (ext h)
  else
    exact isFalse fun hab => h (congrArg QAdjoin.coeffs hab)

/-- Boolean zero test on canonical coordinates. -/
@[expose]
def isZero (a : QAdjoin p x) : Bool :=
  a.coeffs.isZero

instance : Zero (QAdjoin p x) where
  zero := ⟨0, by simpa using x.posDegree⟩

instance : One (QAdjoin p x) where
  one := ⟨1, by
    change (DensePoly.C (1 : Rat)).degree?.getD 0 < p.degree?.getD 0
    rw [DensePoly.degree?_C_getD]
    exact x.posDegree⟩

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

/-- Inversion in a checked irreducible presentation, with `0⁻¹ = 0`. The
one-sided extended gcd tracks only the Bezout coefficient used for the inverse;
the constant-gcd check is a defensive executable guard whose failure is
unreachable under checked irreducibility. -/
@[expose]
def inv [ZPoly.CheckedIrreducible p] (a : QAdjoin p x) : QAdjoin p x :=
  if a.isZero then
    0
  else
    let r := DensePoly.xgcdLeft a.coeffs (ZPoly.toRatPoly p)
    if r.gcd.size = 1 then
      let c := r.gcd.leadingCoeff
      if c = 0 then
        Hex.panicWith 0 "QAdjoin.inv: zero constant gcd"
      else
        reduce p x (DensePoly.scale c⁻¹ r.left)
    else
      Hex.panicWith 0 "QAdjoin.inv: nonconstant gcd"

instance [ZPoly.CheckedIrreducible p] : Inv (QAdjoin p x) := ⟨inv⟩

/-- Division in a checked irreducible presentation. -/
@[expose]
def div [ZPoly.CheckedIrreducible p] (a b : QAdjoin p x) : QAdjoin p x :=
  a * b⁻¹

instance [ZPoly.CheckedIrreducible p] : Div (QAdjoin p x) := ⟨div⟩

/-! Compiled arithmetic regressions in `ℚ[X]/(X²-2)`. -/

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, by decide⟩, by decide⟩

private def sqrtTwoRoot : SimpleRoot sqrtTwoPoly :=
  SimpleRoot.mk sqrtTwoRep

example : LawfulBEq (QAdjoin sqrtTwoPoly sqrtTwoRoot) := inferInstance

#guard
    reduceCoeffs sqrtTwoPoly (DensePoly.ofList ([0, 0, 1] : List Rat)) =
      DensePoly.C 2

#guard
    let xPoly := DensePoly.ofList ([0, 1] : List Rat)
    reduceCoeffs sqrtTwoPoly (xPoly * xPoly) = DensePoly.C 2

#guard
    let xPoly := DensePoly.ofList ([0, 1] : List Rat)
    let x : QAdjoin sqrtTwoPoly sqrtTwoRoot := reduce sqrtTwoPoly sqrtTwoRoot xPoly
    let two : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
      reduce sqrtTwoPoly sqrtTwoRoot (DensePoly.C 2)
    (x * x).coeffs = two.coeffs && x != 0 &&
      (x + x).coeffs = ((2 : Rat) • x).coeffs

-- Construct the checked instance through the executable decision so this
-- regression reaches the shipped inverse and division implementations without
-- adding a proof axiom or a test-only `sorry`.
#guard
    if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
        ⟨hirred, by decide⟩
      let xPoly := DensePoly.ofList ([0, 1] : List Rat)
      let x : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
        reduce sqrtTwoPoly sqrtTwoRoot xPoly
      x * x⁻¹ = 1 && x / x = 1 &&
        (0 : QAdjoin sqrtTwoPoly sqrtTwoRoot)⁻¹ = 0
    else
      false

private def nonmonicQuadratic : ZPoly := DensePoly.ofList [-1, 0, 2]

#guard
    let xPoly := DensePoly.ofList ([0, 1] : List Rat)
    reduceCoeffs nonmonicQuadratic (xPoly * xPoly) = DensePoly.C (1 / 2)

#guard
    let xPoly := DensePoly.ofList ([0, 1] : List Rat)
    let r := DensePoly.xgcdLeft xPoly (ZPoly.toRatPoly nonmonicQuadratic)
    let candidate :=
      reduceCoeffs nonmonicQuadratic
        (DensePoly.scale r.gcd.leadingCoeff⁻¹ r.left)
    candidate = DensePoly.ofList ([0, 2] : List Rat) &&
      reduceCoeffs nonmonicQuadratic (xPoly * candidate) = 1

end Hex.QAdjoin
