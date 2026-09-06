/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.IntegerRoots
public import HexNumberField.Roots

public section

/-!
Exact primitives on canonical algebraic numbers that only need the stored
isolations: the imaginary unit, complex conjugation, and the exact order on
real numbers. Each works at a fixed precision derived from `mahlerPrec`, at
which the approximation balls of two distinct roots of one polynomial are
disjoint, so no API here refines without bound.
-/

namespace Hex.AlgebraicNumber

/-- A precision at which the approximation balls of two distinct roots of `p`
are disjoint: `mahlerPrec p` separates the roots by more than four ball radii
at `mahlerPrec p`, and two more bits leave room for the centre errors. -/
@[expose]
def separationPrec (p : ZPoly) : Int :=
  (mahlerPrec p : Int) + 2

/-- The imaginary unit: the root of `X² + 1` whose stored isolation lies in
the upper half plane. -/
@[expose]
def I : AlgebraicNumber :=
  ((ZPoly.algebraicRoots #p[1, 0, 1]).find? fun a => 0 < a.rep.1.square.im).getD
    (Hex.panicWith 0 "AlgebraicNumber.I: imaginary unit not found")

/-- The mirror image of a ball in the real axis. -/
@[expose]
def mirrorBall (b : DyadicComplexBall) : DyadicComplexBall :=
  { b with im := -b.im }

/-- Complex conjugation. A real number is its own conjugate. Otherwise the
conjugate is a root of the same minimal polynomial, and at `separationPrec`
it is the unique root whose approximation ball meets the mirror image of this
number's ball. -/
@[expose]
def conj (a : AlgebraicNumber) : AlgebraicNumber :=
  if a.isReal then a
  else
    let prec := separationPrec a.p
    let mirror := mirrorBall (a.approx prec)
    ((ZPoly.algebraicRoots a.p).find? fun c => (c.approx prec).meets mirror).getD
      (Hex.panicWith 0 "AlgebraicNumber.conj: conjugate root not found")

/-- Exact comparison of two real algebraic numbers. Equal numbers compare
equal; distinct ones are distinct roots of the product of their minimal
polynomials, whose approximation balls at `separationPrec` of that product are
disjoint, so the order of the ball centres is the order of the numbers. -/
@[expose]
def realCompare (a b : AlgebraicNumber) : Ordering :=
  if a == b then .eq
  else
    let prec := separationPrec (a.p * b.p)
    if (a.approx prec).re < (b.approx prec).re then .lt else .gt

end Hex.AlgebraicNumber

namespace Hex

namespace AlgebraicNumber

/-- The rational point `re + im·i` as an algebraic number. -/
@[expose]
def ofPoint (re im : Rat) : AlgebraicNumber :=
  ofRat re + ofRat im * I

/-- The squared distance from `re + im·i` to `a`, as an exact real algebraic
number: `(a − z)(ā − z̄)`. -/
@[expose]
def distSqTo (a : AlgebraicNumber) (re im : Rat) : AlgebraicNumber :=
  (a - ofPoint re im) * (a.conj - ofPoint re (-im))

/-- Absolute value of a rational. -/
@[expose]
def absRat (q : Rat) : Rat := if q < 0 then -q else q

/-- The squared distance from `re + im·i` to a ball's centre. -/
@[expose]
def ballDistSq (b : DyadicComplexBall) (re im : Rat) : Rat :=
  (b.re.toRat - re) * (b.re.toRat - re) + (b.im.toRat - im) * (b.im.toRat - im)

/-- A square-root-free upper bound on the distance from `re + im·i` to a
ball's centre: the sum of the absolute coordinate differences. -/
@[expose]
def ballDistBound (b : DyadicComplexBall) (re im : Rat) : Rat :=
  absRat (b.re.toRat - re) + absRat (b.im.toRat - im)

/-- Upper bound on the squared distance from `re + im·i` to a ball's points:
`d + 2rl + r²` with `d` the squared centre distance, `r` the radius and `l`
the centre distance bound. -/
@[expose]
def ballUpper (b : DyadicComplexBall) (re im : Rat) : Rat :=
  let r := b.radius.toRat
  ballDistSq b re im + 2 * r * ballDistBound b re im + r * r

/-- Lower bound on the squared distance from `re + im·i` to a ball's points:
`d − 2rl + r²` when the ball does not reach the point (`r² ≤ d`), else `0`. -/
@[expose]
def ballLower (b : DyadicComplexBall) (re im : Rat) : Rat :=
  let r := b.radius.toRat
  if r * r ≤ ballDistSq b re im then
    ballDistSq b re im - 2 * r * ballDistBound b re im + r * r
  else 0

/-- Whether `a` is certified nearer to `re + im·i` than every other listed
root, by ball bounds alone. -/
@[expose]
def certifiedNearest (roots : Array AlgebraicNumber) (a : AlgebraicNumber)
    (prec : Int) (re im : Rat) : Bool :=
  let upper := ballUpper (a.approx prec) re im
  roots.all fun c => c == a || upper < ballLower (c.approx prec) re im

/-- One step of the exact choice: keep the incumbent unless the candidate is
strictly nearer. -/
@[expose]
def exactStep (re im : Rat) (best : Option AlgebraicNumber) (c : AlgebraicNumber) :
    Option AlgebraicNumber :=
  match best with
  | none => some c
  | some b =>
    if (c.distSqTo re im).realCompare (b.distSqTo re im) == .lt then some c else some b

/-- The exact choice: the first root in the array order whose squared
distance to the point is minimal. -/
@[expose]
def exactNearest (roots : Array AlgebraicNumber) (re im : Rat) :
    Option AlgebraicNumber :=
  roots.foldl (exactStep re im) none

end AlgebraicNumber

namespace ZPoly

/-- The root of `p` nearest to `re + im·i`; among roots at the same distance,
the first in `algebraicRoots` order. The fast path certifies a nearest root
from approximation balls at `AlgebraicNumber.separationPrec p`; when that
fails, because two roots are nearly or exactly equidistant, the exact squared
distances decide. A constant polynomial has no roots and yields `0`.

Irreducible, like `algebraicRoots`: a type such as `QAdjoin (rootNear p re)`
is reduced by `#eval` while it looks for a printing instance, and must not
run the root search symbolically. Proofs unfold it explicitly. -/
@[expose, irreducible]
def rootNear (p : ZPoly) (re : Rat) (im : Rat := 0) : AlgebraicNumber :=
  let roots := algebraicRoots p
  let prec := AlgebraicNumber.separationPrec p
  match roots.find? fun a => AlgebraicNumber.certifiedNearest roots a prec re im with
  | some a => a
  | none =>
    (AlgebraicNumber.exactNearest roots re im).getD
      (Hex.panicWith 0 "ZPoly.rootNear: the polynomial has no roots")

end ZPoly

namespace AlgebraicNumber

namespace Display

/-- `q` truncated toward zero to `digits` decimal places, as a Lean literal:
an integer when the fraction is zero, otherwise `d.ddd`, negatives in
parentheses. A display helper; it carries no contract. -/
def decimal (q : Rat) (digits : Nat) : String :=
  let scale : Nat := 10 ^ digits
  let n : Nat := (q.num.natAbs * scale) / q.den
  let whole := n / scale
  let frac := n % scale
  let body :=
    if frac = 0 then s!"{whole}"
    else
      let fracString := toString frac
      let padded := "".pushn '0' (digits - fracString.length) ++ fracString
      s!"{whole}.{padded}"
  if q.num < 0 && n ≠ 0 then s!"(-{body})" else body

/-- Decimal places at which a truncated isolation centre still names its
root: `10 ^ -digits ≤ 2 ^ -mahlerPrec`, so the printed point is within
`(1 + √2) · 2 ^ -mahlerPrec` of the root, less than half the root
separation. -/
def digitsFor (mahler : Nat) : Nat :=
  mahler / 3 + 1

end Display

/-- A canonical number prints as the expression that rebuilds it:
`ZPoly.rootNear p re` for a real number and `ZPoly.rootNear p re im`
otherwise, with `re` and `im` the stored isolation centre truncated to
`digitsFor (mahlerPrec p)` decimals, few enough to read and enough that the
printed point is nearer to this root than to any other
(`rootNear_of_close`). -/
instance : Repr AlgebraicNumber where
  reprPrec a _ :=
    let s := a.rep.1.square
    let digits := Display.digitsFor (mahlerPrec a.p)
    let re := Display.decimal s.re.toRat digits
    let point :=
      if a.isReal then re
      else re ++ " " ++ Display.decimal s.im.toRat digits
    Std.Format.text s!"ZPoly.rootNear {repr a.p} {point}"

end AlgebraicNumber

end Hex
