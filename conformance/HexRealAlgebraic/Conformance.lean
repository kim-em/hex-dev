/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraic
public meta import HexNumberField.Nearest
public meta import HexRealAlgebraic.Basic
public meta import HexRealAlgebraic.Order
public meta import HexRealAlgebraic.Roots
public meta import HexRealAlgebraic.Complex
public meta import HexRealAlgebraic.Norm
import all HexRealAlgebraic.Basic
meta import all HexRealAlgebraic.Basic
import all HexRealAlgebraic.Order
meta import all HexRealAlgebraic.Order

import all HexNumberField.Basic
import all HexNumberField.Nearest

public section

/-!
Oracle: none (core); exact python-flint qqbar arithmetic and certified FLINT root balls
(CI/local).
Mode: always (core); `if_available` (CI), required under `HEX_REQUIRE_ORACLES=1`;
required (local).
Covered operations:
- Checked/proof-taking construction, casts, field arithmetic, powers and scalars.
- Comparison, extrema, sign, abs, conjugation and square roots.
- Fixed-field coordinate signs (`signField`), checked in `FieldSignConformance`.
- Polynomial construction/conversion, roots and root-set membership/projection; integer roots.
- Rounding, rational recognition, dyadic approximation and Repr round trips.
- Complex normSq/abs and real/imaginary projections.
Covered properties:
- Exact order and arithmetic identities, equal construction paths and positive-root selection.
- Root multiplicities and approximation enclosures.
- Fixed-field signs agree with canonical signs across positive and negative embeddings.
Covered edge cases:
- Zero, division by zero, negative rationals, empty/constant polynomials and trailing zeros.
- Nonreal roots/coefficients, close roots, irrational coefficients and repeated roots.
This module, `ReprChecks` and `FieldSignConformance` elaborate in CI. The emitter runs `Checks.run`,
including Mignotte and degree-eight fixtures; local fixtures add degree twelve
and deterministic randomized construction paths.
-/

open Hex
open Hex.RealAlgebraicNumber (ofRat ofAlgebraic? sqrt?)

#guard
  let z : RealAlgebraicNumber := 0
  compare z z == .eq && !(decide (z < z)) && decide (z ≤ z) &&
    min z z == z && max z z == z && z.sign == 0 && z.abs == z &&
    z.toRat? == some 0 && z.floor == 0 && z.ceil == 0 && z⁻¹ == z && z / z == z

#guard
  let q := ofRat (-3 / 2)
  compare q 0 == .lt && compare 0 q == .gt && decide (q < 0) &&
    !(decide (0 < q)) && decide (q ≤ 0) && !(decide (0 ≤ q)) &&
    min q 0 == q && max q 0 == 0 && q.sign == -1 && q.abs == ofRat (3 / 2) &&
    q.toRat? == some (-3 / 2) && q.floor == -2 && q.ceil == -1 &&
    q + q == -3 && q - q == 0 && q * q == ofRat (9 / 4) &&
    q / q == 1 && q⁻¹ == ofRat (-2 / 3) && q ^ (2 : Nat) == q * q &&
    q ^ (-1 : Int) == q⁻¹ && (2 : Nat) • q == -3 && (-2 : Int) • q == 3 &&
    (2 : Rat) • q == -3

#guard
  match ofAlgebraic? (ZPoly.rootNear #p[-2, 0, 1] (3 / 2)),
      ofAlgebraic? (ZPoly.rootNear #p[-8, 0, 1] 3) with
  | some s, some t =>
    let e := t / 2
    compare (-s) s == .lt && compare s (-s) == .gt &&
      compare s (ofRat (7071 / 5000)) == .gt &&
      compare s (ofRat (14143 / 10000)) == .lt &&
      s == e && compare s e == .eq && decide (s ≤ e) && decide (e ≤ s) &&
      !(decide (s < e)) && !(decide (e < s)) && min s e == s && max s e == s &&
      s * s == 2 && (s + 1) - s == 1 && s.sign == 1 && s.abs == s &&
      s.toRat?.isNone && s.floor == 1 && s.ceil == 2 && (-s).floor == -2 &&
      (-s).ceil == -1 && s.conj == s
  | _, _ => false

#guard
  let roots := ZPoly.algebraicRoots #p[1, 0, 1]
  roots.size == 2 && roots.all (fun a => (ofAlgebraic? a).isNone) &&
    (RealAlgebraicPoly.ofAlgebraic?
      (AlgebraicPoly.ofArray #[AlgebraicNumber.I])).isNone

#guard
  match (RealAlgebraicPoly.ofArray #[]).roots,
      (RealAlgebraicPoly.ofArray #[1]).roots,
      (RealAlgebraicPoly.ofArray #[1, 0, 1]).roots with
  | .all, .finite constant, .finite imaginary => constant.isEmpty && imaginary.isEmpty
  | _, _, _ => false

#guard
  (sqrt? (-1)).isNone && sqrt? 0 == some 0 &&
    sqrt? (ofRat (9 / 4)) == some (ofRat (3 / 2))

#guard
  let z : RealAlgebraicNumber := 0
  RealAlgebraicNumber.ofAlgebraic z.toAlgebraic z.property == z &&
    RealAlgebraicNumber.ofRoot? z.toAlgebraic.toRoot == some z &&
    (RealAlgebraicNumber.ofRoot? AlgebraicNumber.I.toRoot).isNone

-- Exercise proof-taking and lazy-root construction on zero, a negative
-- rational, and an irrational real; conjugation and real projections preserve
-- each value, and imaginary projection vanishes.
#guard
  let s := (ofAlgebraic? (ZPoly.rootNear #p[-2, 0, 1] (3 / 2))).getD 0
  (#[0, ofRat (-3 / 2), s]).all fun a =>
    RealAlgebraicNumber.ofAlgebraic a.toAlgebraic a.property == a &&
    RealAlgebraicNumber.ofRoot? a.toAlgebraic.toRoot == some a &&
    a.conj == a && a.toAlgebraic.re == a && a.toAlgebraic.im == 0

#guard
  let a := ofRat (9 / 4)
  let checked := if h : 0 ≤ a then some (a.sqrt h) else none
  checked == some (ofRat (3 / 2)) && checked == a.sqrt? &&
    (RealAlgebraicNumber.sqrt 0 (by decide +kernel)) == 0

#guard
  let a := ofRat (-3 / 2)
  let c := ofRat (a.approx 8).toRat
  let e := ofRat (Dyadic.ofIntWithPrec 1 8).toRat
  decide (c - e ≤ a) && decide (a ≤ c + e) &&
    (ZPoly.realAlgebraicRoots #p[-1, 1]) == #[1] &&
    (ZPoly.realAlgebraicRoots #p[]).isEmpty &&
    (RealAlgebraicPoly.ofArray #[1, 0, 0]).roots.toArray.isEmpty

-- Rational inputs retain the linear canonical representation even after field
-- arithmetic; the real wrapper must not require a real-closure extension.
#guard
  (#[(-7 : Rat) / 3, 0, 1 / (2 ^ (100 : Nat) : Rat)]).all fun q =>
    let a := ofRat q
    a.toAlgebraic.p.natDegree == 1 && a.toRat? == some q &&
      (a + 1).toRat? == some (q + 1) &&
      (a * a).toRat? == some (q * q) &&
      (a - a).toRat? == some 0

#guard
  let roots := (RealAlgebraicPoly.ofArray #[1, -2, 1]).roots
  roots.finite?.isSome && roots.toArray.size == 1 &&
    roots.toArray.all (fun r => r.multiplicity == 2) &&
    roots.contains 1 && !(roots.contains 0) && !(roots.contains (-1))

#guard
  (RealAlgebraicPoly.ofArray #[]).roots.finite?.isNone &&
    ((RealAlgebraicPoly.ofArray #[7]).roots.finite?.map Array.isEmpty) == some true &&
    (RealAlgebraicPoly.ofAlgebraic?
      (AlgebraicPoly.ofArray #[])).isSome

#guard
  let a := AlgebraicNumber.ofRat (-3 / 2)
  let z := AlgebraicNumber.ofRat 0
  a.normSq == ofRat (9 / 4) && a.abs == ofRat (3 / 2) &&
    z.normSq == 0 && z.abs == 0 &&
    AlgebraicNumber.I.normSq == 1 && AlgebraicNumber.I.abs == 1

-- Irrational values on both sides of positive and negative integers.
#guard
  let s := (Hex.RealAlgebraicNumber.ofAlgebraic?
    (Hex.ZPoly.rootNear #p[-2, 0, 1] (3 / 2))).getD 0
  let e := s * Hex.RealAlgebraicNumber.ofRat (1 / (2 ^ (12 : Nat) : Rat))
  (#[1 + e, 1 - e, -1 + e, -1 - e]).map (fun a => (a.floor, a.ceil)) ==
    #[(1, 2), (0, 1), (-1, 0), (-2, -1)]

-- Three field/scalar dictionary cases and nonnegative square-root branches.
#guard
  let s := (sqrt? 2).getD 0
  (#[0, ofRat (-3 / 2), s]).all fun a =>
    a + 0 == a && a - a == 0 && a * 1 == a && -(-a) == a &&
    a ^ (2 : Nat) == a * a && a ^ (-1 : Int) == a⁻¹ &&
    (2 : Nat) • a == a + a && (-2 : Int) • a == -(a + a) &&
    (2 : Rat) • a == a + a &&
    (if a == 0 then a / a == 0 else a / a == 1)

#guard
  (#[0, ofRat (9 / 4), 2]).all fun a =>
    if h : 0 ≤ a then
      let r := a.sqrt h
      r * r == a && decide (0 ≤ r) && a.sqrt? == some r
    else false

#guard
  (#[#[], #[ofRat (-3 / 2)], #[0, -1, 1]] : Array (Array RealAlgebraicNumber)).all
    fun coeffs => match RealAlgebraicPoly.ofAlgebraic?
        (AlgebraicPoly.ofArray (coeffs.map RealAlgebraicNumber.toAlgebraic)) with
      | none => false
      | some p => p.toAlgebraic.coeffs == (RealAlgebraicPoly.ofArray coeffs).toAlgebraic.coeffs

-- Explicit cast operations, including zero and a nontrivial magnitude.
#guard (#[0, 1, 17] : Array Nat).all fun n =>
  (n : RealAlgebraicNumber).toRat? == some (n : Rat)
#guard (#[(-17), 0, 23] : Array Int).all fun n =>
  (n : RealAlgebraicNumber).toRat? == some (n : Rat)

-- Checked conversion must preserve independently known coefficients and trim
-- trailing zero entries, including an irrational coefficient.
#guard
  let r := (sqrt? 2).getD 0
  r * r == 2 &&
    (#[ (#[], #[]), (#[ofRat (-3 / 2), 0, 0], #[ofRat (-3 / 2)]),
        (#[-r, 0, 1, 0, 0], #[-r, 0, 1])] :
      Array (Array RealAlgebraicNumber × Array RealAlgebraicNumber)).all fun (coeffs, expected) =>
    match RealAlgebraicPoly.ofAlgebraic?
        (AlgebraicPoly.ofArray (coeffs.map RealAlgebraicNumber.toAlgebraic)) with
    | none => false
    | some poly =>
      poly.toAlgebraic.coeffs.size == expected.size &&
        poly.toAlgebraic.coeffs == expected.map RealAlgebraicNumber.toAlgebraic
