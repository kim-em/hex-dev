/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyZGcd
import Hex.BenchOracle.Flint
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

/-! Fixed-rung FLINT comparisons. Each target owns a lazy input cache. The
discarded first iteration fills that cache before the timed batch, avoiding
both fixture construction in the measurement and eager construction of every
degree-512 input when the executable starts. -/

def pairToFlintFields (input : PairInput) :
    Array (String × Lean.Json) :=
  #[
    ("a", Hex.BenchOracle.Flint.intsToJson input.left.toArray.toList),
    ("b", Hex.BenchOracle.Flint.intsToJson input.right.toArray.toList)
  ]

def runFlintGcd (input : PairInput) : IO (List Int) := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "gcd"
    (pairToFlintFields input)
  Hex.BenchOracle.Flint.jsonToInts result

def getPair (ref : IO.Ref (Option PairInput)) (prep : Unit → PairInput) :
    IO PairInput := do
  if let some input ← ref.get then
    return input
  let input := prep ()
  ref.set (some input)
  return input

def runLeanFixed (ref : IO.Ref (Option PairInput))
    (prep : Unit → PairInput) (_ : Unit) : IO (List Int) := do
  let input ← getPair ref prep
  return (gcd input.left input.right).toArray.toList

def runFlintFixed (ref : IO.Ref (Option PairInput))
    (prep : Unit → PairInput) (_ : Unit) : IO (List Int) := do
  runFlintGcd (← getPair ref prep)

def runFlintOverhead (_ : Unit) : IO Int := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "overhead" #[]
  match result.getInt? with
  | .ok value => return value
  | .error message =>
      throw <| IO.userError s!"FLINT overhead result not integer: {message}"

initialize coprime8Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize coprime16Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize coprime32Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize coprime64Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize coprime128Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize coprime256Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize coprime512Ref : IO.Ref (Option PairInput) ← IO.mkRef none

initialize dense8_16Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense8_32Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense8_64Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense8_128Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense8_256Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense8_512Ref : IO.Ref (Option PairInput) ← IO.mkRef none

initialize dense256_16Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense256_32Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense256_64Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense256_128Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense256_256Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense256_512Ref : IO.Ref (Option PairInput) ← IO.mkRef none

def runLeanCoprime8 : Unit → IO (List Int) :=
  runLeanFixed coprime8Ref fun _ => prepCoprime 8
def runFlintCoprime8 : Unit → IO (List Int) :=
  runFlintFixed coprime8Ref fun _ => prepCoprime 8
def runLeanCoprime16 : Unit → IO (List Int) :=
  runLeanFixed coprime16Ref fun _ => prepCoprime 16
def runFlintCoprime16 : Unit → IO (List Int) :=
  runFlintFixed coprime16Ref fun _ => prepCoprime 16
def runLeanCoprime32 : Unit → IO (List Int) :=
  runLeanFixed coprime32Ref fun _ => prepCoprime 32
def runFlintCoprime32 : Unit → IO (List Int) :=
  runFlintFixed coprime32Ref fun _ => prepCoprime 32
def runLeanCoprime64 : Unit → IO (List Int) :=
  runLeanFixed coprime64Ref fun _ => prepCoprime 64
def runFlintCoprime64 : Unit → IO (List Int) :=
  runFlintFixed coprime64Ref fun _ => prepCoprime 64
def runLeanCoprime128 : Unit → IO (List Int) :=
  runLeanFixed coprime128Ref fun _ => prepCoprime 128
def runFlintCoprime128 : Unit → IO (List Int) :=
  runFlintFixed coprime128Ref fun _ => prepCoprime 128
def runLeanCoprime256 : Unit → IO (List Int) :=
  runLeanFixed coprime256Ref fun _ => prepCoprime 256
def runFlintCoprime256 : Unit → IO (List Int) :=
  runFlintFixed coprime256Ref fun _ => prepCoprime 256
def runLeanCoprime512 : Unit → IO (List Int) :=
  runLeanFixed coprime512Ref fun _ => prepCoprime 512
def runFlintCoprime512 : Unit → IO (List Int) :=
  runFlintFixed coprime512Ref fun _ => prepCoprime 512

def runLeanDense8_16 : Unit → IO (List Int) :=
  runLeanFixed dense8_16Ref fun _ => prepDense8 16
def runFlintDense8_16 : Unit → IO (List Int) :=
  runFlintFixed dense8_16Ref fun _ => prepDense8 16
def runLeanDense8_32 : Unit → IO (List Int) :=
  runLeanFixed dense8_32Ref fun _ => prepDense8 32
def runFlintDense8_32 : Unit → IO (List Int) :=
  runFlintFixed dense8_32Ref fun _ => prepDense8 32
def runLeanDense8_64 : Unit → IO (List Int) :=
  runLeanFixed dense8_64Ref fun _ => prepDense8 64
def runFlintDense8_64 : Unit → IO (List Int) :=
  runFlintFixed dense8_64Ref fun _ => prepDense8 64
def runLeanDense8_128 : Unit → IO (List Int) :=
  runLeanFixed dense8_128Ref fun _ => prepDense8 128
def runFlintDense8_128 : Unit → IO (List Int) :=
  runFlintFixed dense8_128Ref fun _ => prepDense8 128
def runLeanDense8_256 : Unit → IO (List Int) :=
  runLeanFixed dense8_256Ref fun _ => prepDense8 256
def runFlintDense8_256 : Unit → IO (List Int) :=
  runFlintFixed dense8_256Ref fun _ => prepDense8 256
def runLeanDense8_512 : Unit → IO (List Int) :=
  runLeanFixed dense8_512Ref fun _ => prepDense8 512
def runFlintDense8_512 : Unit → IO (List Int) :=
  runFlintFixed dense8_512Ref fun _ => prepDense8 512

def runLeanDense256_16 : Unit → IO (List Int) :=
  runLeanFixed dense256_16Ref fun _ => prepDense256 16
def runFlintDense256_16 : Unit → IO (List Int) :=
  runFlintFixed dense256_16Ref fun _ => prepDense256 16
def runLeanDense256_32 : Unit → IO (List Int) :=
  runLeanFixed dense256_32Ref fun _ => prepDense256 32
def runFlintDense256_32 : Unit → IO (List Int) :=
  runFlintFixed dense256_32Ref fun _ => prepDense256 32
def runLeanDense256_64 : Unit → IO (List Int) :=
  runLeanFixed dense256_64Ref fun _ => prepDense256 64
def runFlintDense256_64 : Unit → IO (List Int) :=
  runFlintFixed dense256_64Ref fun _ => prepDense256 64
def runLeanDense256_128 : Unit → IO (List Int) :=
  runLeanFixed dense256_128Ref fun _ => prepDense256 128
def runFlintDense256_128 : Unit → IO (List Int) :=
  runFlintFixed dense256_128Ref fun _ => prepDense256 128
def runLeanDense256_256 : Unit → IO (List Int) :=
  runLeanFixed dense256_256Ref fun _ => prepDense256 256
def runFlintDense256_256 : Unit → IO (List Int) :=
  runFlintFixed dense256_256Ref fun _ => prepDense256 256
def runLeanDense256_512 : Unit → IO (List Int) :=
  runLeanFixed dense256_512Ref fun _ => prepDense256 512
def runFlintDense256_512 : Unit → IO (List Int) :=
  runFlintFixed dense256_512Ref fun _ => prepDense256 512

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

def leanCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 10.0, warmupFirstIter := true,
    minTotalSeconds := 0.2 }

def flintCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 10.0, warmupFirstIter := true,
    minTotalSeconds := 0.2 }

setup_fixed_benchmark runFlintOverhead where flintCompareConfig

setup_fixed_benchmark runLeanCoprime8 where leanCompareConfig
setup_fixed_benchmark runFlintCoprime8 where flintCompareConfig
setup_fixed_benchmark runLeanCoprime16 where leanCompareConfig
setup_fixed_benchmark runFlintCoprime16 where flintCompareConfig
setup_fixed_benchmark runLeanCoprime32 where leanCompareConfig
setup_fixed_benchmark runFlintCoprime32 where flintCompareConfig
setup_fixed_benchmark runLeanCoprime64 where leanCompareConfig
setup_fixed_benchmark runFlintCoprime64 where flintCompareConfig
setup_fixed_benchmark runLeanCoprime128 where leanCompareConfig
setup_fixed_benchmark runFlintCoprime128 where flintCompareConfig
setup_fixed_benchmark runLeanCoprime256 where leanCompareConfig
setup_fixed_benchmark runFlintCoprime256 where flintCompareConfig
setup_fixed_benchmark runLeanCoprime512 where leanCompareConfig
setup_fixed_benchmark runFlintCoprime512 where flintCompareConfig

setup_fixed_benchmark runLeanDense8_16 where leanCompareConfig
setup_fixed_benchmark runFlintDense8_16 where flintCompareConfig
setup_fixed_benchmark runLeanDense8_32 where leanCompareConfig
setup_fixed_benchmark runFlintDense8_32 where flintCompareConfig
setup_fixed_benchmark runLeanDense8_64 where leanCompareConfig
setup_fixed_benchmark runFlintDense8_64 where flintCompareConfig
setup_fixed_benchmark runLeanDense8_128 where leanCompareConfig
setup_fixed_benchmark runFlintDense8_128 where flintCompareConfig
setup_fixed_benchmark runLeanDense8_256 where leanCompareConfig
setup_fixed_benchmark runFlintDense8_256 where flintCompareConfig
setup_fixed_benchmark runLeanDense8_512 where leanCompareConfig
setup_fixed_benchmark runFlintDense8_512 where flintCompareConfig

setup_fixed_benchmark runLeanDense256_16 where leanCompareConfig
setup_fixed_benchmark runFlintDense256_16 where flintCompareConfig
setup_fixed_benchmark runLeanDense256_32 where leanCompareConfig
setup_fixed_benchmark runFlintDense256_32 where flintCompareConfig
setup_fixed_benchmark runLeanDense256_64 where leanCompareConfig
setup_fixed_benchmark runFlintDense256_64 where flintCompareConfig
setup_fixed_benchmark runLeanDense256_128 where leanCompareConfig
setup_fixed_benchmark runFlintDense256_128 where flintCompareConfig
setup_fixed_benchmark runLeanDense256_256 where leanCompareConfig
setup_fixed_benchmark runFlintDense256_256 where flintCompareConfig
setup_fixed_benchmark runLeanDense256_512 where leanCompareConfig
setup_fixed_benchmark runFlintDense256_512 where flintCompareConfig

end Hex.PolyZGcdBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
