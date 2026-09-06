/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.IntegerRoots

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
