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
external JSONL profile. Mode: `if_available`.

Covered operations:
- fixed-presentation `QAdjoin.reduce`, arithmetic, inversion, division, and
  threaded approximation, plus checked and total canonical conversion;
- lazy `AlgebraicRoot` negation, addition, subtraction, multiplication,
  inversion, division, and exactification in both checked and total forms;
- canonical `AlgebraicNumber` arithmetic through its public instances;
- canonical rational construction, casts, scalar action, and powers;
- semantic equality of lazy values represented by different polynomials;
- checked and total fixed-field and algebraic-coefficient root APIs;
- `ZPoly.algebraicRoots?`/`algebraicRoots`, the reality test `isReal`, the
  output order `rootLe`, `approx`, and the `Repr` display.

Covered properties and edge cases:
- `sqrt(2)^2 = 2`, `sqrt(2) * sqrt(2)^-1 = 1`, and `0^-1 = 0`;
- `sqrt(2) + sqrt(2)`, `sqrt(2) * sqrt(2)`, cancellation with the opposite
  conjugate, and arithmetic with the independent root `sqrt(3)`;
- zero multiplication/inversion and the reciprocal of a very small root;
- exactification through an enclosing polynomial with an irrelevant factor;
- equal values with different nonminimal polynomials and a conjugate-embedding
  impostor that must compare unequal;
- zero, constant, linear, and repeated-root polynomial conventions;
- `algebraicRoots` on `X^2 - 2` (order `-sqrt(2), sqrt(2)`), on
  `(X^2 - 2)^2 (X + 3)` (multiplicity dropped, `-3` first), on `X^3 - 2` (the
  real root first, then the conjugate pair), and on the zero, constant, and
  `X` polynomials; `isReal` on a real root, a nonreal root, and zero.
-/

namespace Hex.NumberFieldConformance

open Hex

/-! # Selected-root fixtures -/

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

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
  ⟨⟨negSqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

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
  ⟨⟨sqrtThreeSquare, .ofWitness (by decide)⟩, by decide⟩

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

private def tinyPoly : ZPoly := DensePoly.ofList [-1, 1024]

private def tinySquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 1 10, 0, 16⟩

private def tinyRep : RefinedIsolation tinyPoly :=
  ⟨⟨tinySquare, .ofWitness (by decide)⟩, by decide⟩

private def tiny? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots tinyPoly then
    some
      { p := tinyPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk tinyRep
        rep := tinyRep
        rep_mk := rfl }
  else
    none

private def twoWithZeroPoly : ZPoly := DensePoly.ofList [0, -2, 1]

private def twoWithZeroSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 2 0, 0, 8⟩

private def twoWithZeroRep : RefinedIsolation twoWithZeroPoly :=
  ⟨⟨twoWithZeroSquare, .ofWitness (by decide)⟩, by decide⟩

private def twoWithZero? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots twoWithZeroPoly then
    some
      { p := twoWithZeroPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk twoWithZeroRep
        rep := twoWithZeroRep
        rep_mk := rfl }
  else
    none

private def enclosingPoly : ZPoly :=
  sqrtTwoPoly * DensePoly.ofList [-3, 1]

private def enclosingSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 6074001000 32, 0, 32⟩

private def enclosingRep : RefinedIsolation enclosingPoly :=
  ⟨⟨enclosingSquare, .ofWitness (by decide)⟩, by decide⟩

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

private def sqrtTwoExact? : Option AlgebraicNumber :=
  sqrtTwo? >>= AlgebraicRoot.exact?

private def sqrtThreeExact? : Option AlgebraicNumber :=
  sqrtThree? >>= AlgebraicRoot.exact?

/-! # Fixed-presentation arithmetic and approximation -/

#guard
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    let xPoly := DensePoly.ofList ([0, 1] : List Rat)
    let x : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
      QAdjoin.reduce sqrtTwoPoly sqrtTwoRoot xPoly
    let two : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
      QAdjoin.reduce sqrtTwoPoly sqrtTwoRoot (DensePoly.C 2)
    x + x = (2 : Rat) • x && x - x = 0 && -x + x = 0 &&
      (3 / 2 : Rat) • x = x + (1 / 2 : Rat) • x &&
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

/-! # Lazy algebraic arithmetic -/

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
            decide (3 < sum.rep.1.square.re) &&
            decide (0 < product.rep.1.square.re) &&
            decide (-1 < difference.rep.1.square.re) &&
            decide (difference.rep.1.square.re < 0)
      | _, _, _ => false
  | _, _ => false

-- The primary total wrappers execute the same certified paths and negation
-- reflects both the polynomial and selected isolation.
#guard
  match sqrtTwo?, sqrtThree? with
  | some a, some b =>
      let negated := a.neg
      let sum := a.add b
      let difference := a.sub b
      let product := a.mul b
      let inverse := a.inv
      let quotient := a.div a
      negated.p = sqrtTwoPoly && negated.rep.1.square = negSqrtTwoSquare &&
        sum.p = DensePoly.ofList [1, 0, -10, 0, 1] &&
        difference.p = DensePoly.ofList [1, 0, -10, 0, 1] &&
        product.p = DensePoly.ofList [-6, 0, 1] &&
        inverse.p = DensePoly.ofList [-1, 0, 2] &&
        quotient.p = DensePoly.ofList [-1, 0, 1]
  | _, _ => false

-- Reciprocal amplification for a small nonzero rational root and removal of
-- the irrelevant `X` factor introduced by an unselected zero conjugate.
#guard
  match tiny?, sqrtTwo?, twoWithZero? with
  | some tiny, some sqrtTwo, some two =>
      tiny.inv.p = DensePoly.ofList [-1024, 1] &&
        (tiny.inv?).map (fun inverse => inverse.p) =
          some (DensePoly.ofList [-1024, 1]) &&
        (sqrtTwo.mul two).p = DensePoly.ofList [-8, 0, 1] &&
        (sqrtTwo.mul? two).map (fun product => product.p) =
          some (DensePoly.ofList [-8, 0, 1]) &&
        two.inv.p = DensePoly.ofList [-1, 2] &&
        (two.inv?).map (fun inverse => inverse.p) =
          some (DensePoly.ofList [-1, 2])
  | _, _, _ => false

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

/-! # Exactification and semantic identity -/

#guard
  match enclosingRoot? with
  | some a =>
      match a.exact? with
      | some exact => exact.p = sqrtTwoPoly && a.exact.p = sqrtTwoPoly
      | none => false
  | none => false

-- Canonical arithmetic is the user-facing field-like API, not merely a
-- consequence inferred from checked lazy operations.
#guard
  match sqrtTwoExact?, sqrtThreeExact? with
  | some a, some b =>
      (a + b).p = DensePoly.ofList [1, 0, -10, 0, 1] &&
        (a - b).p = DensePoly.ofList [1, 0, -10, 0, 1] &&
        (a * b).p = DensePoly.ofList [-6, 0, 1] &&
        (-a).p = sqrtTwoPoly && a⁻¹.p = DensePoly.ofList [-1, 0, 2] &&
        (a / a).p = DensePoly.ofList [-1, 1] &&
        (a - a).isZero && (a * 0).isZero &&
        ((0 : AlgebraicNumber)⁻¹).isZero && (a / 0).isZero
  | _, _ => false

-- Canonical rational construction supplies the ordinary executable field
-- surface used by the companion's law-bearing instance.
#guard
  let one : AlgebraicNumber := 1
  let two : AlgebraicNumber := 2
  let negTwo : AlgebraicNumber := AlgebraicNumber.ofRat (-2)
  AlgebraicNumber.ofRat 0 == 0 &&
    one == AlgebraicNumber.ofRat 1 &&
    two == one + one && negTwo == -two &&
    ((5 : Nat) : AlgebraicNumber) == AlgebraicNumber.ofRat 5 &&
    ((-5 : Int) : AlgebraicNumber) == AlgebraicNumber.ofRat (-5) &&
    ((3 : Rat) • one) == AlgebraicNumber.ofRat 3 &&
    ((3 : Nat) • one) == AlgebraicNumber.ofRat 3 &&
    ((-3 : Int) • two) == AlgebraicNumber.ofRat (-6) &&
    one ^ (7 : Nat) == one && two ^ (0 : Int) == one &&
    two ^ (-1 : Int) == AlgebraicNumber.ofRat (1 / 2)

#guard
  match sqrtTwoExact? with
  | some a => a ^ (2 : Nat) == AlgebraicNumber.ofRat 2
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

/-! # Polynomial roots -/

private def fixedSqrtTwo : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
  QAdjoin.reduce sqrtTwoPoly sqrtTwoRoot
    (DensePoly.ofList ([0, 1] : List Rat))

private def fixedLinear : DensePoly (QAdjoin sqrtTwoPoly sqrtTwoRoot) :=
  DensePoly.ofList [-fixedSqrtTwo, 1]

-- Both checked and total fixed-presentation conversions retain the selected
-- root and round-trip the canonical generator coordinate.
#guard
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    let total := fixedSqrtTwo.toAlgebraicNumber sqrtTwoRep rfl
    match fixedSqrtTwo.toAlgebraicNumber? sqrtTwoRep rfl with
    | some checked =>
        checked.p = sqrtTwoPoly && total.p = sqrtTwoPoly &&
          checked.toQAdjoin.coeffs = fixedSqrtTwo.coeffs &&
          checked.toRoot.p = sqrtTwoPoly
    | none => false
  else
    false

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

-- The primary total fixed-field root wrapper preserves the repeated bucket.
#guard
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    match QAdjoin.roots (fixedLinear * fixedLinear) sqrtTwoRep rfl with
    | .finite roots =>
        roots.size = 1 &&
          (roots[0]?).map (fun root => root.multiplicity) = some 2
    | .all => false
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

/-! # Algebraic-coefficient polynomials -/

private def algebraicOne? : Option AlgebraicNumber :=
  AlgebraicPoly.Common.rational? 1

private def algebraicLinear? : Option AlgebraicPoly := do
  let sqrtTwo ← sqrtTwoExact?
  let one ← algebraicOne?
  some (AlgebraicPoly.ofArray #[-sqrtTwo, one])

private def algebraicRepeated? : Option AlgebraicPoly := do
  let sqrtTwo ← sqrtTwoExact?
  let one ← algebraicOne?
  let two ← AlgebraicPoly.Common.rational? 2
  some (AlgebraicPoly.ofArray #[two, -(sqrtTwo + sqrtTwo), one])

-- Typical linear input exercises semantic coefficient storage and both the
-- checked and total algebraic-coefficient root entry points.
#guard
  match algebraicLinear? with
  | some polynomial =>
      polynomial.coeffs.size = 2 && polynomial.degree? = some 1 &&
        !polynomial.isZero &&
        match polynomial.roots?, polynomial.roots with
        | some (.finite checked), .finite total =>
            checked.size = 1 && total.size = 1 &&
              (checked[0]?).any fun root =>
                root.multiplicity = 1 && root.root.p = sqrtTwoPoly
        | _, _ => false
  | none => false

-- Zero and nonzero constants take their explicit `.all` and empty branches;
-- trailing semantic zeros are removed by `AlgebraicPoly.ofArray`.
#guard
  match algebraicOne? with
  | some one =>
      let zero := AlgebraicPoly.ofArray #[0, 0, 0]
      let constant := AlgebraicPoly.ofArray #[one, 0]
      zero.isZero && zero.coeffs.isEmpty && constant.degree? = some 0 &&
        match zero.roots?, zero.roots, constant.roots?, constant.roots with
        | some .all, .all, some (.finite checked), .finite total =>
            checked.isEmpty && total.isEmpty
        | _, _, _, _ => false
  | none => false

-- A repeated algebraic linear factor retains its one root with multiplicity
-- two after primitive-presentation construction and Yun decomposition.
#guard
  match algebraicRepeated? with
  | some polynomial =>
      match polynomial.roots?, polynomial.roots with
      | some (.finite checked), .finite total =>
          checked.size = 1 && total.size = 1 &&
            (checked[0]?).map (fun root => root.multiplicity) = some 2 &&
            (total[0]?).map (fun root => root.multiplicity) = some 2
      | _, _ => false
  | none => false


/-! # Roots of integer polynomials -/

-- `X^2 - 2`: two real roots, `-sqrt(2)` before `sqrt(2)`, both canonical, and
-- the total wrapper agrees with the checked form.
#guard
  let p : ZPoly := #p[-2, 0, 1]
  match ZPoly.algebraicRoots? p with
  | some roots =>
      roots.size = 2 && ZPoly.algebraicRoots p == roots &&
        roots.all (fun a => a.p = p && a.isReal) &&
        (roots[0]?).map (fun a => decide ((a.approx 24).re < 0)) = some true &&
        (roots[1]?).map (fun a => decide ((a.approx 24).re > 0)) = some true &&
        (roots[0]?).map (fun a => a == -roots[1]!) = some true
  | none => false

-- `(X^2 - 2)^2 (X + 3)`: multiplicity is dropped, the rational root `-3`
-- comes first because it is the smallest real root, and the two surds keep
-- their canonical minimal polynomial.
#guard
  let p : ZPoly := #p[-2, 0, 1] * #p[-2, 0, 1] * #p[3, 1]
  let roots := ZPoly.algebraicRoots p
  roots.size = 3 &&
    (roots[0]?).map (fun a => a == AlgebraicNumber.ofRat (-3)) = some true &&
    (roots[1]?).map (fun a => a.p = #p[-2, 0, 1] && a.isReal) = some true &&
    (roots[2]?).map (fun a => a.p = #p[-2, 0, 1] && a.isReal) = some true

-- `X^3 - 2`: the real cube root first, then the conjugate pair, which is
-- nonreal, and the three roots sum to zero.
#guard
  let p : ZPoly := #p[-2, 0, 0, 1]
  let roots := ZPoly.algebraicRoots p
  roots.size = 3 &&
    (roots[0]?).map (fun a => a.isReal) = some true &&
    (roots[1]?).map (fun a => !a.isReal) = some true &&
    (roots[2]?).map (fun a => !a.isReal) = some true &&
    roots.all (fun a => a.p = p) &&
    (roots.foldl (· + ·) 0 == 0)

-- The zero polynomial, a nonzero constant, and `X` take their stated
-- branches: no roots, no roots, and the canonical zero (which is real).
#guard
  ZPoly.algebraicRoots? (0 : ZPoly) == some #[] &&
    ZPoly.algebraicRoots? (#p[7] : ZPoly) == some #[] &&
    (match ZPoly.algebraicRoots? (#p[0, 1] : ZPoly) with
      | some roots => roots.size = 1 &&
          (roots[0]?).map (fun a => a == 0 && a.isReal) = some true
      | none => false)

-- `sqrt(2) + sqrt(3)` through the public entry point has the expected
-- minimal polynomial, its inverse is `sqrt(3) - sqrt(2)`, and the display
-- is the expression that rebuilds the number.
#guard
  let s2 := (ZPoly.algebraicRoots #p[-2, 0, 1])[1]!
  let s3 := (ZPoly.algebraicRoots #p[-3, 0, 1])[1]!
  (s2 + s3).p = #p[1, 0, -10, 0, 1] && (s2 + s3)⁻¹ == s3 - s2 &&
    (repr s2).pretty == "ZPoly.rootNear #p[-2, 0, 1] 1.414" &&
    (repr (s2 + s3)).pretty == "ZPoly.rootNear #p[1, 0, -10, 0, 1] 3.146264369"

-- The exact primitives: the imaginary unit squares to `-1`, conjugation
-- fixes real numbers and negates the imaginary unit, and the real order is
-- exact, including on values that only agree after canonicalization.
#guard
  let s2 := (ZPoly.algebraicRoots #p[-2, 0, 1])[1]!
  let s3 := (ZPoly.algebraicRoots #p[-3, 0, 1])[1]!
  AlgebraicNumber.I * AlgebraicNumber.I == -1 &&
    AlgebraicNumber.conj (s2 + AlgebraicNumber.I) == s2 - AlgebraicNumber.I &&
    AlgebraicNumber.conj s2 == s2 &&
    AlgebraicNumber.realCompare s2 s3 == .lt &&
    AlgebraicNumber.realCompare s3 s2 == .gt &&
    AlgebraicNumber.realCompare (s3 - s2) ((s2 + s3)⁻¹) == .eq &&
    AlgebraicNumber.realCompare (-s2) s2 == .lt

-- The nearest root: from an approximation, from a point equidistant from two
-- roots (the first in output order wins), and from the real axis for a
-- conjugate pair; and the display rebuilds the number.
#guard
  let s2 := (ZPoly.algebraicRoots #p[-2, 0, 1])[1]!
  let s3 := (ZPoly.algebraicRoots #p[-3, 0, 1])[1]!
  ZPoly.rootNear #p[-2, 0, 1] 1.4 == s2 &&
    ZPoly.rootNear #p[1, 0, -10, 0, 1] 3.15 == s2 + s3 &&
    ZPoly.rootNear #p[1, 0, 1] 0 0.9 == AlgebraicNumber.I &&
    ZPoly.rootNear #p[-2, 0, 1] 0 == -s2 &&
    ZPoly.rootNear #p[1, 0, 1] 5 == -AlgebraicNumber.I &&
    (repr s2).pretty == "ZPoly.rootNear #p[-2, 0, 1] 1.414" &&
    (repr (s2 + s3)).pretty == "ZPoly.rootNear #p[1, 0, -10, 0, 1] 3.146264369"

end Hex.NumberFieldConformance
