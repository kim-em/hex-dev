/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyZGcd
import LeanBench

/-!
Native scientific benchmarks for `hex-poly-z-gcd`.

The registrations separate the five input families required by the SPEC:

* coprime pairs settled by the one-image route;
* dense inputs with a gcd of half the ambient degree, at 8- and 256-bit
  coefficient widths;
* coefficient-swell inputs measured through the deterministic PRS route;
* the fast integer and reference rational squarefree decompositions on the
  same Berlekamp--Zassenhaus-shaped inputs;
* rational gcd after denominator clearing.

All polynomial construction is outside the timed region. Timed targets return
compact hashes that force the complete result.
-/

namespace Hex.PolyZGcdBench

open Hex
open Hex.ZPoly

instance : Hashable ZPoly where
  hash p := hash p.toArray

def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

def hashPoly (p : ZPoly) : UInt64 :=
  p.toArray.foldl (fun acc coefficient => mixWord acc (hash coefficient)) 0

def hashRatPoly (p : DensePoly Rat) : UInt64 :=
  p.toArray.foldl (fun acc coefficient => mixWord acc (hash coefficient)) 0

def hashDecomp (d : PrimitiveSquareFreeDecomposition) : UInt64 :=
  mixWord (hashPoly d.primitive)
    (mixWord (hashPoly d.squareFreeCore) (hashPoly d.repeatedPart))

/-- A deterministic nonzero coefficient with the requested approximate bit
width. The small bounded perturbation prevents the dense fixtures from having
an accidental common scalar content. -/
def coefficient (bits degree index salt : Nat) : Int :=
  let low := Int.ofNat (((index + 3) * (salt + 17) + degree * 29) % 251 + 1)
  let magnitude :=
    if bits <= 8 then low
    else (2 : Int) ^ (bits - 1) + low
  if (index + salt) % 2 = 0 then magnitude else -magnitude

/-- Deterministic exact-degree dense integer polynomial. -/
def densePoly (degree bits salt : Nat) : ZPoly :=
  DensePoly.ofCoeffs <| (Array.range (degree + 1)).map fun index =>
    coefficient bits degree index salt

structure PairInput where
  left : ZPoly
  right : ZPoly
  deriving Hashable

/-- Equal-degree coprime inputs. `right = left + 1`, so their gcd is exactly
one over every coefficient field where the degrees are preserved. -/
def prepCoprime (degree : Nat) : PairInput :=
  let left := densePoly degree 8 11
  { left, right := left + 1 }

/-- Dense inputs of ambient degree about `degree`, sharing a factor of degree
`degree / 2`; the cofactors differ by one and are therefore coprime. -/
def prepDense (bits degree : Nat) : PairInput :=
  let common := densePoly (degree / 2) bits 31
  let leftCofactor := densePoly (degree - degree / 2) bits 47
  let rightCofactor := leftCofactor + 1
  { left := common * leftCofactor, right := common * rightCofactor }

def prepDense8 (degree : Nat) : PairInput :=
  prepDense 8 degree

def prepDense256 (degree : Nat) : PairInput :=
  prepDense 256 degree

/-- A small-degree PRS fixture with large, alternating coefficients. The
inputs share a nonmonic linear factor; the remaining dense cofactors make the
extended subresultant recurrence carry the coefficient swell. -/
def prepSwell (bits : Nat) : PairInput :=
  let common : ZPoly := DensePoly.ofList [3, 2]
  let leftCofactor := densePoly 12 bits 71
  let rightCofactor := densePoly 11 bits 89
  { left := common * leftCofactor, right := common * rightCofactor }

/-- A Berlekamp--Zassenhaus-shaped squarefree input with one repeated linear
factor and many distinct linear factors. -/
def prepSquarefree (factorCount : Nat) : ZPoly :=
  let repeated : ZPoly := DensePoly.ofList [1, 1]
  (Array.range factorCount).foldl
    (fun product index =>
      product * DensePoly.ofList [Int.ofNat (index + 2), 1])
    (repeated * repeated)

structure RatPairInput where
  left : DensePoly Rat
  right : DensePoly Rat

instance : Hashable RatPairInput where
  hash input := mixWord (hashRatPoly input.left) (hashRatPoly input.right)

/-- The dense-gcd family after independent denominator scaling. -/
def prepRational (degree : Nat) : RatPairInput :=
  let input := prepDense 8 degree
  { left := DensePoly.scale (Rat.divInt 1 101) (toRatPoly input.left)
    right := DensePoly.scale (Rat.divInt 1 103) (toRatPoly input.right) }

def runGcd (input : PairInput) : UInt64 :=
  hashPoly (gcd input.left input.right)

def runCoprimeGcd (input : PairInput) : UInt64 :=
  runGcd input

/-- The one-image work against which the coprime dispatch is priced. -/
def runCoprimeImage (input : PairInput) : UInt64 :=
  let supply : Array ZMod64.Prime := ZMod64.primesBelow 47 1
  if h : 0 < supply.size then
      let p : ZMod64.Prime := supply[0]
      letI : ZMod64.Bounds p.m := p.bounds
      letI : ZMod64.PrimeModulus p.m := ZMod64.primeModulusOfPrime p.prime
      let left := reduceModP p.m input.left
      let right := reduceModP p.m input.right
      let image := DensePoly.gcd left right
      image.toArray.foldl
        (fun acc coefficient => mixWord acc coefficient.toUInt64) 0
  else
    0

def runDense8 (input : PairInput) : UInt64 :=
  runGcd input

def runDense256 (input : PairInput) : UInt64 :=
  runGcd input

def runSwellPrs (input : PairInput) : UInt64 :=
  match prsCert? input.left input.right with
  | none => 0
  | some cert =>
      mixWord (hashPoly cert.gcd)
        (mixWord (hashPoly cert.cofL) (hashPoly cert.cofR))

def runSqfFast (input : ZPoly) : UInt64 :=
  hashDecomp (sqfDecomp input)

def runSqfRational (input : ZPoly) : UInt64 :=
  hashDecomp (primitiveSquareFreeDecomposition input)

def runRatGcd (input : RatPairInput) : UInt64 :=
  hashRatPoly (ratGcd input.left input.right)

/- One modular image performs two linear reductions. The dense field gcd is
quadratic in the degree on the current generic `FpPoly` implementation. -/
setup_benchmark runCoprimeImage n => n * n
  with prep := prepCoprime
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Route 1 performs one image gcd and one linear certificate replay, hence the
same quadratic degree model as the image baseline. -/
setup_benchmark runCoprimeGcd n => n * n
  with prep := prepCoprime
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Brown image gcds and candidate divisions are quadratic in ambient degree;
the 8-bit family varies only degree. -/
setup_benchmark runDense8 n => n * n
  with prep := prepDense8
  where {
    paramSchedule := .custom #[16, 32, 64, 128, 256, 512]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- The coefficient width is fixed at 256 bits, so the scientific scaling axis
remains the quadratic polynomial degree. -/
setup_benchmark runDense256 n => n * n
  with prep := prepDense256
  where {
    paramSchedule := .custom #[16, 32, 64, 128, 256, 512]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Degree is fixed and the parameter is coefficient bit width. The integral
PRS recurrence performs a fixed number of big-integer operations whose limb
cost is represented by `b * sqrt b` on the GMP Karatsuba-range ladder. -/
setup_benchmark runSwellPrs bits => bits * Nat.sqrt bits
  with prep := prepSwell
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- The squarefree input has `n + 2` linear factors. Polynomial multiplication
and the derivative gcd are quadratic in the resulting degree. -/
setup_benchmark runSqfFast n => n * n
  with prep := prepSquarefree
  where {
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Reference rational Euclid on exactly the same squarefree inputs. Its
declared operation-count baseline is quadratic; coefficient swell is expected
to make the measured verdict worse and is reported rather than fitted away. -/
setup_benchmark runSqfRational n => n * n
  with prep := prepSquarefree
  where {
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Denominator clearing is linear and the integer gcd dominates at quadratic
degree cost for the fixed 101/103 denominators. -/
setup_benchmark runRatGcd n => n * n
  with prep := prepRational
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end Hex.PolyZGcdBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
