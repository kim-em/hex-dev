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
the selected root's certified magnitude bound before refining the root once.
-/
namespace Hex

namespace QAdjoin

/-- Horner evaluation of a rational polynomial on the circumscribed disc of a
dyadic square. -/
@[expose]
def evalRatBall (f : DensePoly Rat) (s : DyadicSquare)
    (coeffPrec : Int) : DyadicComplexBall :=
  let z := s.toBall
  let cs := f.toArray
  match cs.back? with
  | none => DyadicComplexBall.zero
  | some top =>
      cs.pop.foldr
        (fun c acc => (DyadicComplexBall.ofRat c coeffPrec).add (z.mul acc))
        (DyadicComplexBall.ofRat top coeffPrec)

/-- Bit-length upper bound for the magnitudes of rational coefficients. Since
every rational denominator is positive, the numerator magnitude alone is a
valid upper bound. -/
@[expose]
def coeffBits (f : DensePoly Rat) : Nat :=
  f.toArray.foldl
    (fun bits q => Nat.max bits (Hex.ceilLog2 (q.num.natAbs + 1))) 0

/-- Bit-length upper bound for the magnitude of every point in a square's
circumscribed disc. The bound is clamped at zero when the disc lies inside the
unit circle. -/
@[expose]
def rootBits (s : DyadicSquare) : Nat :=
  (max 0 (Hex.Dyadic.ceilLog2 (GaussDyadic.hi s.center + s.radiusHi))).toNat

/-- Guard bits sufficient for coefficient rounding and Horner amplification
over the selected root's certified circumscribed disc. -/
@[expose]
def approxGuardBits (s : DyadicSquare) (f : DensePoly Rat) : Nat :=
  8 + Hex.ceilLog2 (f.size + 1) + coeffBits f +
    f.size * (rootBits s + 3)

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
    let b := DyadicComplexBall.ofRat (-1 / 3 : Rat) 4
    b.re = Dyadic.ofIntWithPrec (-6) 4 && b.im = 0 &&
      b.radius = Dyadic.ofIntWithPrec 1 4

#guard
    let a : DyadicComplexBall :=
      ⟨1, 2, Dyadic.ofIntWithPrec 1 3⟩
    let b : DyadicComplexBall :=
      ⟨3, -1, Dyadic.ofIntWithPrec 1 4⟩
    let m := a.mul b
    m.re = 5 && m.im = 5 && m.radius = Dyadic.ofIntWithPrec 89 7

#guard
    let f := DensePoly.ofList ([1, 1] : List Rat)
    let s : DyadicSquare := ⟨2, 0, 10⟩
    let b := evalRatBall f s 16
    b.re = 3 && b.im = 0 && b.radius = s.radiusHi

end QAdjoin
end Hex
