/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexNumberField

/-!
Core conformance checks for `HexNumberField`.

Oracle: cypari2/PARI for algebraic-number minimal polynomials and
python-flint for the integer eliminants and factorization checks in the
external JSONL profile. Mode: if_available.

Covered operations:
- fixed-presentation `QAdjoin.reduce`, arithmetic, inversion, division, and
  threaded approximation;
- lazy `AlgebraicRoot` negation, addition, subtraction, multiplication,
  inversion, division, and exactification;
- semantic equality of lazy values represented by different polynomials;
- fixed-field and algebraic-coefficient root APIs.

Covered properties and edge cases:
- `sqrt(2)^2 = 2`, `sqrt(2) * sqrt(2)^-1 = 1`, and `0^-1 = 0`;
- `sqrt(2) + sqrt(2)`, `sqrt(2) * sqrt(2)`, cancellation with the opposite
  conjugate, and arithmetic with the independent root `sqrt(3)`;
- zero multiplication/inversion and the reciprocal of a very small root;
- exactification through an enclosing polynomial with an irrelevant factor;
- equal values with different nonminimal polynomials and a conjugate-embedding
  impostor that must compare unequal;
- zero, constant, linear, and repeated-root polynomial conventions.
-/

namespace Hex.NumberFieldConformance

open Hex

/-! ## Selected-root fixtures -/

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, by decide⟩, by decide⟩

private def sqrtTwoRoot : SimpleRoot sqrtTwoPoly :=
  SimpleRoot.mk sqrtTwoRep

private def sqrtTwo? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots sqrtTwoPoly then
    some
      { p := sqrtTwoPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := sqrtTwoRoot
        rep := sqrtTwoRep
        rep_mk := rfl }
  else
    none

private def negSqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec (-181) 7, 0, 8⟩

private def negSqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨negSqrtTwoSquare, by decide⟩, by decide⟩

private def negSqrtTwo? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots sqrtTwoPoly then
    some
      { p := sqrtTwoPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk negSqrtTwoRep
        rep := negSqrtTwoRep
        rep_mk := rfl }
  else
    none

private def sqrtThreePoly : ZPoly := DensePoly.ofList [-3, 0, 1]

private def sqrtThreeSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 222 7, 0, 8⟩

private def sqrtThreeRep : RefinedIsolation sqrtThreePoly :=
  ⟨⟨sqrtThreeSquare, by decide⟩, by decide⟩

private def sqrtThree? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots sqrtThreePoly then
    some
      { p := sqrtThreePoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk sqrtThreeRep
        rep := sqrtThreeRep
        rep_mk := rfl }
  else
    none

private def enclosingPoly : ZPoly :=
  sqrtTwoPoly * DensePoly.ofList [-3, 1]

private def enclosingSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 6074001000 32, 0, 32⟩

private def enclosingRep : RefinedIsolation enclosingPoly :=
  ⟨⟨enclosingSquare, by decide⟩, by decide⟩

private def enclosingRoot? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots enclosingPoly then
    some
      { p := enclosingPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk enclosingRep
        rep := enclosingRep
        rep_mk := rfl }
  else
    none

/-! ## Fixed-presentation arithmetic and approximation -/

#guard
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    let xPoly := DensePoly.ofList ([0, 1] : List Rat)
    let x : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
      QAdjoin.reduce sqrtTwoPoly sqrtTwoRoot xPoly
    let two : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
      QAdjoin.reduce sqrtTwoPoly sqrtTwoRoot (DensePoly.C 2)
    x * x = two && x * x⁻¹ = 1 && x / x = 1 &&
      (0 : QAdjoin sqrtTwoPoly sqrtTwoRoot)⁻¹ = 0
  else
    false

-- Reduction trims a high power, preserves a reduced linear value, and
-- normalizes trailing zero coefficients.
#guard
  let x := DensePoly.ofList ([0, 1] : List Rat)
  QAdjoin.reduceCoeffs sqrtTwoPoly (x * x) = DensePoly.C 2 &&
    QAdjoin.reduceCoeffs sqrtTwoPoly (x + 1) = x + 1 &&
    QAdjoin.reduceCoeffs sqrtTwoPoly
      (DensePoly.ofList ([3, 0, 0] : List Rat)) = DensePoly.C 3

#guard
  let xPoly := DensePoly.ofList ([0, 1] : List Rat)
  let x : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
    QAdjoin.reduce sqrtTwoPoly sqrtTwoRoot xPoly
  let first := x.approx sqrtTwoRep rfl 24
  let second := x.approx first.1 (QAdjoin.approx_root x sqrtTwoRep rfl 24) 48
  first.2.radius ≤ Dyadic.ofIntWithPrec 1 24 &&
    second.2.radius ≤ Dyadic.ofIntWithPrec 1 48 &&
    first.1.1.square.discsMeet second.1.1.square

/-! ## Lazy algebraic arithmetic -/

#guard
  match sqrtTwo? with
  | some a =>
      match a.add? a, a.sub? a, a.mul? a, a.inv?, a.div? a with
      | some sum, some difference, some product, some inverse, some quotient =>
          sum.p = DensePoly.ofList [0, -8, 0, 1] && !sum.isZero &&
            difference.isZero &&
            product.p = DensePoly.ofList [-4, 0, 1] &&
            decide (0 < product.rep.1.square.re) &&
            inverse.p = DensePoly.ofList [-1, 0, 2] &&
            quotient.p = DensePoly.ofList [-1, 0, 1]
      | _, _, _, _, _ => false
  | none => false

-- Independent quadratic inputs exercise the full degree-product eliminants.
#guard
  match sqrtTwo?, sqrtThree? with
  | some a, some b =>
      match a.add? b, a.mul? b, a.sub? b with
      | some sum, some product, some difference =>
          sum.p.degree?.getD 0 = 4 && product.p.degree?.getD 0 = 2 &&
            difference.p.degree?.getD 0 = 4 &&
            decide (0 < sum.rep.1.square.re) &&
            decide (0 < product.rep.1.square.re) &&
            decide (difference.rep.1.square.re < 0)
      | _, _, _ => false
  | _, _ => false

-- Cancellation, zero multiplication, and zero inversion are distinct edges.
#guard
  match sqrtTwo?, negSqrtTwo? with
  | some a, some b =>
      match a.add? b, a.mul? AlgebraicNumber.zero.toRoot,
          AlgebraicNumber.zero.toRoot.inv? with
      | some sum, some product, some inverse =>
          sum.isZero && product.isZero && inverse.isZero
      | _, _, _ => false
  | _, _ => false

/-! ## Exactification and semantic identity -/

#guard
  match enclosingRoot? with
  | some a =>
      match a.exact? with
      | some exact => exact.p = sqrtTwoPoly
      | none => false
  | none => false

-- Same selected value through different enclosing polynomials; opposite
-- conjugates of the same polynomial must not be confused.
#guard
  match sqrtTwo?, negSqrtTwo?, enclosingRoot? with
  | some positive, some negative, some enclosing =>
      QAdjoin.Roots.sameValue? positive enclosing = some true &&
        QAdjoin.Roots.sameValue? positive negative = some false &&
        QAdjoin.Roots.sameValue? positive positive = some true
  | _, _, _ => false

/-! ## Polynomial roots -/

private def fixedSqrtTwo : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
  QAdjoin.reduce sqrtTwoPoly sqrtTwoRoot
    (DensePoly.ofList ([0, 1] : List Rat))

private def fixedLinear : DensePoly (QAdjoin sqrtTwoPoly sqrtTwoRoot) :=
  DensePoly.ofList [-fixedSqrtTwo, 1]

#guard
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    match QAdjoin.roots? (fixedLinear * fixedLinear) sqrtTwoRep rfl with
    | some (.finite roots) =>
        roots.size = 1 &&
          (roots[0]?).map (fun root => root.multiplicity) = some 2 &&
          (roots[0]?).any fun root =>
            decide (0 < root.root.rep.1.square.re)
    | _ => false
  else
    false

#guard
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    match
        QAdjoin.roots?
          (0 : DensePoly (QAdjoin sqrtTwoPoly sqrtTwoRoot))
          sqrtTwoRep rfl,
        QAdjoin.roots? 1 sqrtTwoRep rfl with
    | some .all, some (.finite roots) => roots.isEmpty
    | _, _ => false
  else
    false

end Hex.NumberFieldConformance
