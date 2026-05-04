import Hex.Conformance.Emit
import HexPolyZ

/-!
JSONL emit driver for the `hex-poly-z` oracle.

`lake exe hexpolyz_emit_fixtures` writes one fixture record per
input case followed by `result` records carrying Lean's computed
answer for each operation, mirroring the `HexPoly` bootstrap.  The
companion driver `scripts/oracle/polyz_flint.py` re-runs each
operation via python-flint's `fmpz_poly` (`content`, `gcd`, `divmod`,
plus a manually-divided primitive part) and re-derives the Mignotte
coefficient bound from the input coefficients.

Operations covered:

* `content`            — `Hex.ZPoly.content`, value `Int`.
* `primitive_part`     — `Hex.ZPoly.primitivePart`, value coefficient list.
* `gcd_z`              — integer-gcd associate computed via
  `ratPolyPrimitivePart (DensePoly.gcd (toRatPoly f) (toRatPoly g))`.
  The primitive associate is normalised to a non-negative leading
  coefficient so it matches `fmpz_poly.gcd`'s convention.
* `divmod`             — `Hex.DensePoly.divMod` over `Int`.  Lean's
  truncating-integer division only matches `fmpz_poly`'s result when
  the divisor evenly divides the dividend, so we restrict to those
  exact cases (analogous to the `HexPoly` bootstrap).
* `mignotte_coeff_bound` — `Hex.ZPoly.mignotteCoeffBound f k j`,
  emitted alongside `[k, j, bound]` so the oracle can reconstruct
  `binom k j * ceilSqrt (∑ cᵢ²)` from the coefficient list.
-/

namespace Hex.PolyZEmit

open Hex.Conformance.Emit
open Hex.DensePoly

private def lib : String := "HexPolyZ"

/-- Emit a JSON integer literal as a `result.value` payload. -/
private def intValue (n : Int) : String := toString n

/-- Emit a `[k, j, bound]` triple as a JSON array `result.value`. -/
private def mignotteValue (k j : Nat) (bound : Nat) : String :=
  polyValue [(k : Int), (j : Int), (bound : Int)]

private structure ContentCase where
  id     : String
  coeffs : List Int

/-- Content / primitive-part fixtures.  Cases include nontrivial
contents up to 30 over polynomials of degree 8 and 12, plus the
already-primitive and zero edge cases. -/
private def contentCases : List ContentCase := [
  { id := "content/primitive8",
    coeffs := [1, -3, 0, 5, -7, 2, 0, -4, 3] },
  { id := "content/scaled8",
    coeffs := [6, -12, 0, 18, 24, -6, 0, 30, 12] },
  { id := "content/scaled8/sevens",
    coeffs := [14, 0, -7, 21, 7, -28, 49, 0, 7] },
  { id := "content/scaled12",
    coeffs := [30, 60, -90, 30, -30, 0, 60, -150, 30, 0, -30, 90, 30] },
  { id := "content/zero",
    coeffs := [0, 0, 0] }
]

private def emitContentCase (c : ContentCase) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/input") c.coeffs
  let p : ZPoly := DensePoly.ofCoeffs c.coeffs.toArray
  emitResult lib c.id "content" (intValue (ZPoly.content p))
  emitResult lib c.id "primitive_part"
    (polyValue (ZPoly.primitivePart p).toArray.toList)

private structure GcdCase where
  id    : String
  left  : List Int
  right : List Int

/-- GCD-over-Z fixtures: each pair shares a non-trivial integer
factor.  python-flint's `fmpz_poly.gcd` returns the primitive
associate with positive leading coefficient, matching
`ratPolyPrimitivePart (DensePoly.gcd ...)` modulo sign. -/
private def gcdCases : List GcdCase := [
  { id    := "gcd/deg6/sharedQuartic",
    left  := [-36, 0, 49, 0, -14, 0, 1],
    right := [4, 0, -1, 0, -4, 0, 1] },
  { id    := "gcd/deg10/sharedQuartic",
    left  := [-36, 0, 49, 0, -50, 0, 50, 0, -14, 0, 1],
    right := [-4, 0, 5, 0, -1, 0, 4, 0, -5, 0, 1] }
]

private def integerGcd (f g : ZPoly) : ZPoly :=
  ZPoly.ratPolyPrimitivePart (DensePoly.gcd (ZPoly.toRatPoly f) (ZPoly.toRatPoly g))

private def emitGcdCase (c : GcdCase) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/left")  c.left
  emitPolyFixture lib (c.id ++ "/right") c.right
  let f : ZPoly := DensePoly.ofCoeffs c.left.toArray
  let g : ZPoly := DensePoly.ofCoeffs c.right.toArray
  emitResult lib c.id "gcd_z"
    (polyValue (integerGcd f g).toArray.toList)

private structure DivModCase where
  id       : String
  dividend : List Int
  divisor  : List Int

/-- DivMod-over-Z fixtures.  Lean's `Int`-division is truncating, so
we restrict to dividends that the divisor evenly splits — exactly the
regime where Lean and `fmpz_poly` divmod must agree. -/
private def divModCases : List DivModCase := [
  { id       := "divmod/exactDeg8/byQuadratic",
    dividend := [-2, 13, -11, -7, 9, -23, 16, 15, 2],
    divisor  := [-1, 5, 2] },
  { id       := "divmod/exactDeg8/byMonicQuartic",
    dividend := [-1, 2, -6, 7, -15, 1, -12, 5, 5],
    divisor  := [-1, 0, -3, 1, 1] }
]

private def emitDivModCase (c : DivModCase) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/dividend") c.dividend
  emitPolyFixture lib (c.id ++ "/divisor")  c.divisor
  let a : ZPoly := DensePoly.ofCoeffs c.dividend.toArray
  let b : ZPoly := DensePoly.ofCoeffs c.divisor.toArray
  let (q, r) := divMod a b
  emitResult lib c.id "divmod"
    (divModValue q.toArray.toList r.toArray.toList)

private structure MignotteCase where
  id     : String
  coeffs : List Int
  /-- Factor-degree / coefficient-index pairs `(k, j)` to evaluate. -/
  pairs  : List (Nat × Nat)

/-- Mignotte-bound fixtures.  Lean computes
`mignotteCoeffBound f k j = binom k j * ceilSqrt (∑ cᵢ²)`; the oracle
re-derives the same bound from the raw coefficient list and reports a
mismatch if either factor disagrees. -/
private def mignotteCases : List MignotteCase := [
  { id     := "mignotte/deg8/typical",
    coeffs := [3, -4, 5, 0, 1, -2, 0, 7, -1],
    pairs  := [(4, 2), (6, 3), (8, 0)] },
  { id     := "mignotte/deg12/sparse",
    coeffs := [2, 0, -1, 3, 0, 0, 5, 0, -2, 0, 0, 4, 1],
    pairs  := [(6, 3), (10, 5), (12, 0)] }
]

private def emitMignotteCase (c : MignotteCase) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/input") c.coeffs
  let p : ZPoly := DensePoly.ofCoeffs c.coeffs.toArray
  for (k, j) in c.pairs do
    emitResult lib c.id "mignotte_coeff_bound"
      (mignotteValue k j (ZPoly.mignotteCoeffBound p k j))

end Hex.PolyZEmit

def main : IO Unit := do
  for c in Hex.PolyZEmit.contentCases  do Hex.PolyZEmit.emitContentCase  c
  for c in Hex.PolyZEmit.gcdCases      do Hex.PolyZEmit.emitGcdCase      c
  for c in Hex.PolyZEmit.divModCases   do Hex.PolyZEmit.emitDivModCase   c
  for c in Hex.PolyZEmit.mignotteCases do Hex.PolyZEmit.emitMignotteCase c
