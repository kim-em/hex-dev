/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexPolyZGcd.Gcd
public import HexPolyZGcd.Gcd

public section

/-!
Fast primitive square-free normalization driven by the checked integer gcd.
-/

namespace Hex

namespace ZPoly

/-- Integer-gcd replacement for `primitiveSquareFreeDecomposition`'s rational
Euclidean bottleneck.  The return type and normalization convention are shared
with the existing reference implementation. -/
def sqfDecomp (f : ZPoly) : PrimitiveSquareFreeDecomposition :=
  let primitive := primitivePart f
  if primitive.isZero then
    { primitive, squareFreeCore := 0, repeatedPart := 0 }
  else
    let derivative := DensePoly.derivative primitive
    if derivative.isZero then
      { primitive
        squareFreeCore := normalizePrimitiveSign primitive
        repeatedPart := 1 }
    else if primitive.size ≤ 8 then
      -- Below the crossover, constructing and replaying a general certificate
      -- costs more than the rational Euclidean calculation itself.  Reuse its
      -- canonical integer candidate, but recover the core by one integer long
      -- division instead of the reference route's rational division and
      -- denominator clearing.
      let repeatedPart := rationalGcdCandidate primitive derivative
      { primitive
        squareFreeCore := normalizePrimitiveSign (DensePoly.divMod primitive repeatedPart).1
        repeatedPart }
    else
      let cert := gcdCert primitive derivative
      { primitive
        squareFreeCore := normalizePrimitiveSign cert.cofL
        repeatedPart := cert.gcd }

/-- The fast decomposition's repeated part is the checked gcd of the primitive
input and its derivative in the nondegenerate branch. -/
theorem sqfDecomp_repeatedPart (f : ZPoly)
    (hp : (primitivePart f).isZero = false)
    (hd : (DensePoly.derivative (primitivePart f)).isZero = false) :
    (sqfDecomp f).repeatedPart =
      gcd (primitivePart f) (DensePoly.derivative (primitivePart f)) := by
  sorry

/-- The fast square-free core and repeated part reassemble the primitive input
up to the normalization sign. -/
theorem sqfDecomp_reassembly_signed (f : ZPoly) :
    let d := sqfDecomp f
    ∃ ε : Int, (ε = 1 ∨ ε = -1) ∧
      DensePoly.scale ε (d.squareFreeCore * d.repeatedPart) = d.primitive := by
  sorry

/-- Every nonzero fast square-free core is square-free over `Rat[x]`. -/
theorem sqfDecomp_squareFreeCore (f : ZPoly)
    (hcore : (sqfDecomp f).squareFreeCore ≠ 0) :
    SquareFreeRat (sqfDecomp f).squareFreeCore := by
  sorry

#guard
  let x1 : ZPoly := DensePoly.ofList [1, 1]
  let x2 : ZPoly := DensePoly.ofList [2, 1]
  let f := x1 * x1 * x2
  let d := sqfDecomp f
  d.repeatedPart == x1 && d.squareFreeCore == x1 * x2

end ZPoly

end Hex
