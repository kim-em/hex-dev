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
Threaded dyadic-ball approximation for fixed-field elements.

Rational coefficients are rounded downward to dyadics with an explicit
one-ulp radius, then Horner evaluation propagates complex-ball errors. An
input-derived guard-bit budget accounts for coefficient height, degree, and
the defining polynomial's Cauchy root bound before refining the root once.
-/
namespace Hex

namespace DyadicComplexBall

/-- The exact zero complex ball. -/
@[expose]
def zero : DyadicComplexBall := ⟨0, 0, 0⟩

/-- Minkowski sum of two closed dyadic complex balls. -/
@[expose]
def add (a b : DyadicComplexBall) : DyadicComplexBall :=
  ⟨a.re + b.re, a.im + b.im, a.radius + b.radius⟩

/-- Product enclosure for two closed dyadic complex balls. -/
@[expose]
def mul (a b : DyadicComplexBall) : DyadicComplexBall :=
  let ac : GaussDyadic := (a.re, a.im)
  let bc : GaussDyadic := (b.re, b.im)
  let center := GaussDyadic.mul ac bc
  let radius :=
    GaussDyadic.hi ac * b.radius + GaussDyadic.hi bc * a.radius +
      a.radius * b.radius
  ⟨center.1, center.2, radius⟩

/-- Enclose a rational number by a real-centred dyadic complex ball. Exact
dyadic rationals receive radius zero; otherwise one ulp encloses the downward
rounding error. -/
@[expose]
def ofRat (q : Rat) (prec : Int) : DyadicComplexBall :=
  let lo := q.toDyadic prec
  let radius := if lo.toRat = q then 0 else Dyadic.ofIntWithPrec 1 prec
  ⟨lo, 0, radius⟩

end DyadicComplexBall

namespace QAdjoin

/-- Horner evaluation of a rational polynomial on the circumscribed disc of a
dyadic square. -/
@[expose]
def evalRatBall (f : DensePoly Rat) (s : DyadicSquare)
    (coeffPrec : Int) : DyadicComplexBall :=
  let z := s.toBall
  f.toArray.toList.foldr
    (fun c acc => (DyadicComplexBall.ofRat c coeffPrec).add (z.mul acc))
    DyadicComplexBall.zero

/-- Bit-length upper bound for the magnitudes of rational coefficients. Since
every rational denominator is positive, the numerator magnitude alone is a
valid upper bound. -/
@[expose]
def coeffBits (f : DensePoly Rat) : Nat :=
  f.toArray.toList.foldl
    (fun bits q => Nat.max bits (Hex.ceilLog2 (q.num.natAbs + 1))) 0

/-- Guard bits sufficient for coefficient rounding and Horner amplification
over the defining polynomial's Cauchy root bound. -/
@[expose]
def approxGuardBits (p : ZPoly) (f : DensePoly Rat) : Nat :=
  8 + Hex.ceilLog2 (f.size + 1) + coeffBits f +
    f.size * (cauchyExp p + 3)

/-! Compiled ball-arithmetic regressions. -/

#guard
    let a : DyadicComplexBall := ⟨1, 1, 0⟩
    let b : DyadicComplexBall := ⟨1, -1, 0⟩
    let m := a.mul b
    let s := a.add b
    m.re = 2 && m.im = 0 && m.radius = 0 &&
      s.re = 2 && s.im = 0 && s.radius = 0

#guard
    let b := DyadicComplexBall.ofRat (1 / 3 : Rat) 4
    b.re = Dyadic.ofIntWithPrec 5 4 && b.im = 0 &&
      b.radius = Dyadic.ofIntWithPrec 1 4

#guard
    let f := DensePoly.ofList ([1, 1] : List Rat)
    let s : DyadicSquare := ⟨2, 0, 10⟩
    let b := evalRatBall f s 16
    b.re = 3 && b.im = 0 && b.radius = s.radiusHi

end QAdjoin
end Hex
