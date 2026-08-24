/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyZGcd
import Hex.BenchOracle.Flint
import HexBasic.Rand
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
width. Two mixed words replace the earlier affine coefficient stream: affine
streams make successive dense remainders live in a tiny linear span and turn
the generic Euclidean fixture into a short-quotient special case. -/
def coefficient (bits degree index salt : Nat) : Int :=
  let seed := degree * 0x9E3779B9 + index * 0x85EBCA6B + salt * 0xC2B2AE35
  let first := (Rand.ofSeed seed).next
  let word := first.1
  let extra := first.2.next.1
  let payload : Nat :=
    if bits <= 65 then
      word.toNat % (2 ^ (bits - 1))
    else
      word.toNat * 2 ^ (bits - 65) +
        extra.toNat % (2 ^ (bits - 65))
  let magnitude :=
    (2 : Int) ^ (bits - 1) + Int.ofNat payload
  if word.toNat % 2 = 0 then magnitude else -magnitude

/-- Deterministic exact-degree dense integer polynomial. -/
def densePoly (degree bits salt : Nat) : ZPoly :=
  DensePoly.ofCoeffs <| (Array.range (degree + 1)).map fun index =>
    coefficient bits degree index salt

structure PairInput where
  left : ZPoly
  right : ZPoly
  deriving Hashable

/-- Independent deterministic equal-degree inputs. Their checked gcd is one;
unlike an adjacent pair, they exercise the full modular Euclidean path rather
than terminating after a constant first remainder. -/
def prepCoprime (degree : Nat) : PairInput :=
  let left := densePoly degree 8 11
  { left, right := densePoly degree 8 19 }

/-- Adjacent coprime inputs used only for the like-for-like FLINT gate. The
generic scientific family above remains the asymptotic and internal-reference
evidence, so this short-quotient comparator is not the sole route-1 fixture. -/
def prepCoprimeCompare (degree : Nat) : PairInput :=
  let left := densePoly degree 8 11
  { left, right := left + 1 }

/-- Dense inputs of ambient degree about `degree`, sharing a factor of degree
`degree / 2`. Independent deterministic cofactors avoid the one-remainder
best case of rational Euclid while retaining a reproducible generic dense
family. -/
def prepDense (bits degree : Nat) : PairInput :=
  let common := densePoly (degree / 2) bits 31
  let leftCofactor := densePoly (degree - degree / 2) bits 47
  let rightCofactor := densePoly (degree - degree / 2) bits 59
  { left := common * leftCofactor, right := common * rightCofactor }

/-- Dense common-factor inputs with adjacent cofactors for the fixed FLINT
ladder. Generic independent cofactors remain in `prepDense` for the scientific
and rational-reference tracks. -/
def prepDenseCompare (bits degree : Nat) : PairInput :=
  let common := densePoly (degree / 2) bits 31
  let leftCofactor := densePoly (degree - degree / 2) bits 47
  { left := common * leftCofactor, right := common * (leftCofactor + 1) }

def prepDense8 (degree : Nat) : PairInput :=
  prepDense 8 degree

def prepDense256 (degree : Nat) : PairInput :=
  prepDense 256 degree

def prepDense8Compare (degree : Nat) : PairInput :=
  prepDenseCompare 8 degree

def prepDense256Compare (degree : Nat) : PairInput :=
  prepDenseCompare 256 degree

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
      let image := FpPoly.gcdCached left right
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

def runRationalFixed (ref : IO.Ref (Option PairInput))
    (prep : Unit → PairInput) (_ : Unit) : IO (List Int) := do
  let input ← getPair ref prep
  return (rationalGcdCandidate input.left input.right).toArray.toList

def getPoly (ref : IO.Ref (Option ZPoly)) (prep : Unit → ZPoly) : IO ZPoly := do
  if let some input ← ref.get then
    return input
  let input := prep ()
  ref.set (some input)
  return input

def runFastSqfFixed (ref : IO.Ref (Option ZPoly))
    (prep : Unit → ZPoly) (_ : Unit) : IO UInt64 := do
  return runSqfFast (← getPoly ref prep)

def runRationalSqfFixed (ref : IO.Ref (Option ZPoly))
    (prep : Unit → ZPoly) (_ : Unit) : IO UInt64 := do
  return runSqfRational (← getPoly ref prep)

def runFlintOverhead (_ : Unit) : IO Int := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "overhead" #[]
  match result.getInt? with
  | .ok value => return value
  | .error message =>
      throw <| IO.userError s!"FLINT overhead result not integer: {message}"

initialize coprime64Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize coprime128Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize coprime256Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize coprime512Ref : IO.Ref (Option PairInput) ← IO.mkRef none

initialize genericCoprime16Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize genericCoprime32Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize genericCoprime64Ref : IO.Ref (Option PairInput) ← IO.mkRef none

initialize dense8_64Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense8_128Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense8_256Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense8_512Ref : IO.Ref (Option PairInput) ← IO.mkRef none

initialize genericDense8_16Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize genericDense8_32Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize genericDense8_64Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize genericDense8_128Ref : IO.Ref (Option PairInput) ← IO.mkRef none

initialize dense256_64Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense256_128Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense256_256Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize dense256_512Ref : IO.Ref (Option PairInput) ← IO.mkRef none

initialize genericDense256_16Ref : IO.Ref (Option PairInput) ← IO.mkRef none
initialize genericDense256_32Ref : IO.Ref (Option PairInput) ← IO.mkRef none

initialize swell512Ref : IO.Ref (Option PairInput) ← IO.mkRef none

initialize sqf2Ref : IO.Ref (Option ZPoly) ← IO.mkRef none
initialize sqf4Ref : IO.Ref (Option ZPoly) ← IO.mkRef none
initialize sqf8Ref : IO.Ref (Option ZPoly) ← IO.mkRef none
initialize sqf16Ref : IO.Ref (Option ZPoly) ← IO.mkRef none
initialize sqf32Ref : IO.Ref (Option ZPoly) ← IO.mkRef none
initialize sqf64Ref : IO.Ref (Option ZPoly) ← IO.mkRef none
initialize sqf128Ref : IO.Ref (Option ZPoly) ← IO.mkRef none

def runLeanGenericCoprime16 : Unit → IO (List Int) :=
  runLeanFixed genericCoprime16Ref fun _ => prepCoprime 16
def runRationalCoprime16 : Unit → IO (List Int) :=
  runRationalFixed genericCoprime16Ref fun _ => prepCoprime 16
def runLeanGenericCoprime32 : Unit → IO (List Int) :=
  runLeanFixed genericCoprime32Ref fun _ => prepCoprime 32
def runRationalCoprime32 : Unit → IO (List Int) :=
  runRationalFixed genericCoprime32Ref fun _ => prepCoprime 32
def runLeanCoprime64 : Unit → IO (List Int) :=
  runLeanFixed coprime64Ref fun _ => prepCoprimeCompare 64
def runFlintCoprime64 : Unit → IO (List Int) :=
  runFlintFixed coprime64Ref fun _ => prepCoprimeCompare 64
def runLeanGenericCoprime64 : Unit → IO (List Int) :=
  runLeanFixed genericCoprime64Ref fun _ => prepCoprime 64
def runRationalCoprime64 : Unit → IO (List Int) :=
  runRationalFixed genericCoprime64Ref fun _ => prepCoprime 64
def runLeanCoprime128 : Unit → IO (List Int) :=
  runLeanFixed coprime128Ref fun _ => prepCoprimeCompare 128
def runFlintCoprime128 : Unit → IO (List Int) :=
  runFlintFixed coprime128Ref fun _ => prepCoprimeCompare 128
def runLeanCoprime256 : Unit → IO (List Int) :=
  runLeanFixed coprime256Ref fun _ => prepCoprimeCompare 256
def runFlintCoprime256 : Unit → IO (List Int) :=
  runFlintFixed coprime256Ref fun _ => prepCoprimeCompare 256
def runLeanCoprime512 : Unit → IO (List Int) :=
  runLeanFixed coprime512Ref fun _ => prepCoprimeCompare 512
def runFlintCoprime512 : Unit → IO (List Int) :=
  runFlintFixed coprime512Ref fun _ => prepCoprimeCompare 512

def runLeanGenericDense8_16 : Unit → IO (List Int) :=
  runLeanFixed genericDense8_16Ref fun _ => prepDense8 16
def runRationalDense8_16 : Unit → IO (List Int) :=
  runRationalFixed genericDense8_16Ref fun _ => prepDense8 16
def runLeanGenericDense8_32 : Unit → IO (List Int) :=
  runLeanFixed genericDense8_32Ref fun _ => prepDense8 32
def runRationalDense8_32 : Unit → IO (List Int) :=
  runRationalFixed genericDense8_32Ref fun _ => prepDense8 32
def runLeanDense8_64 : Unit → IO (List Int) :=
  runLeanFixed dense8_64Ref fun _ => prepDense8Compare 64
def runFlintDense8_64 : Unit → IO (List Int) :=
  runFlintFixed dense8_64Ref fun _ => prepDense8Compare 64
def runLeanGenericDense8_64 : Unit → IO (List Int) :=
  runLeanFixed genericDense8_64Ref fun _ => prepDense8 64
def runRationalDense8_64 : Unit → IO (List Int) :=
  runRationalFixed genericDense8_64Ref fun _ => prepDense8 64
def runLeanDense8_128 : Unit → IO (List Int) :=
  runLeanFixed dense8_128Ref fun _ => prepDense8Compare 128
def runFlintDense8_128 : Unit → IO (List Int) :=
  runFlintFixed dense8_128Ref fun _ => prepDense8Compare 128
def runLeanGenericDense8_128 : Unit → IO (List Int) :=
  runLeanFixed genericDense8_128Ref fun _ => prepDense8 128
def runRationalDense8_128 : Unit → IO (List Int) :=
  runRationalFixed genericDense8_128Ref fun _ => prepDense8 128
def runLeanDense8_256 : Unit → IO (List Int) :=
  runLeanFixed dense8_256Ref fun _ => prepDense8Compare 256
def runFlintDense8_256 : Unit → IO (List Int) :=
  runFlintFixed dense8_256Ref fun _ => prepDense8Compare 256
def runLeanDense8_512 : Unit → IO (List Int) :=
  runLeanFixed dense8_512Ref fun _ => prepDense8Compare 512
def runFlintDense8_512 : Unit → IO (List Int) :=
  runFlintFixed dense8_512Ref fun _ => prepDense8Compare 512

def runLeanGenericDense256_16 : Unit → IO (List Int) :=
  runLeanFixed genericDense256_16Ref fun _ => prepDense256 16
def runRationalDense256_16 : Unit → IO (List Int) :=
  runRationalFixed genericDense256_16Ref fun _ => prepDense256 16
def runLeanGenericDense256_32 : Unit → IO (List Int) :=
  runLeanFixed genericDense256_32Ref fun _ => prepDense256 32
def runRationalDense256_32 : Unit → IO (List Int) :=
  runRationalFixed genericDense256_32Ref fun _ => prepDense256 32
def runLeanDense256_64 : Unit → IO (List Int) :=
  runLeanFixed dense256_64Ref fun _ => prepDense256Compare 64
def runFlintDense256_64 : Unit → IO (List Int) :=
  runFlintFixed dense256_64Ref fun _ => prepDense256Compare 64
def runLeanDense256_128 : Unit → IO (List Int) :=
  runLeanFixed dense256_128Ref fun _ => prepDense256Compare 128
def runFlintDense256_128 : Unit → IO (List Int) :=
  runFlintFixed dense256_128Ref fun _ => prepDense256Compare 128
def runLeanDense256_256 : Unit → IO (List Int) :=
  runLeanFixed dense256_256Ref fun _ => prepDense256Compare 256
def runFlintDense256_256 : Unit → IO (List Int) :=
  runFlintFixed dense256_256Ref fun _ => prepDense256Compare 256
def runLeanDense256_512 : Unit → IO (List Int) :=
  runLeanFixed dense256_512Ref fun _ => prepDense256Compare 512
def runFlintDense256_512 : Unit → IO (List Int) :=
  runFlintFixed dense256_512Ref fun _ => prepDense256Compare 512

def runLeanSwell512 : Unit → IO (List Int) :=
  runLeanFixed swell512Ref fun _ => prepSwell 512
def runRationalSwell512 : Unit → IO (List Int) :=
  runRationalFixed swell512Ref fun _ => prepSwell 512

def runFastSqf2 : Unit → IO UInt64 :=
  runFastSqfFixed sqf2Ref fun _ => prepSquarefree 2
def runRationalSqf2 : Unit → IO UInt64 :=
  runRationalSqfFixed sqf2Ref fun _ => prepSquarefree 2
def runFastSqf4 : Unit → IO UInt64 :=
  runFastSqfFixed sqf4Ref fun _ => prepSquarefree 4
def runRationalSqf4 : Unit → IO UInt64 :=
  runRationalSqfFixed sqf4Ref fun _ => prepSquarefree 4
def runFastSqf8 : Unit → IO UInt64 :=
  runFastSqfFixed sqf8Ref fun _ => prepSquarefree 8
def runRationalSqf8 : Unit → IO UInt64 :=
  runRationalSqfFixed sqf8Ref fun _ => prepSquarefree 8
def runFastSqf16 : Unit → IO UInt64 :=
  runFastSqfFixed sqf16Ref fun _ => prepSquarefree 16
def runRationalSqf16 : Unit → IO UInt64 :=
  runRationalSqfFixed sqf16Ref fun _ => prepSquarefree 16
def runFastSqf32 : Unit → IO UInt64 :=
  runFastSqfFixed sqf32Ref fun _ => prepSquarefree 32
def runRationalSqf32 : Unit → IO UInt64 :=
  runRationalSqfFixed sqf32Ref fun _ => prepSquarefree 32
def runFastSqf64 : Unit → IO UInt64 :=
  runFastSqfFixed sqf64Ref fun _ => prepSquarefree 64
def runRationalSqf64 : Unit → IO UInt64 :=
  runRationalSqfFixed sqf64Ref fun _ => prepSquarefree 64
def runFastSqf128 : Unit → IO UInt64 :=
  runFastSqfFixed sqf128Ref fun _ => prepSquarefree 128
def runRationalSqf128 : Unit → IO UInt64 :=
  runRationalSqfFixed sqf128Ref fun _ => prepSquarefree 128

/- A dense image gcd uses quadratic long division over the fixed word-sized
field. The result hash is linear and therefore lower order. -/
setup_benchmark runCoprimeImage n => n * n
  with prep := prepCoprime
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048,
      4096, 8192, 16384]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.5
  }

/- Route 1 performs the dense image gcd above, normalizes its Bezout identity,
and replays products of degree `n`; all use quadratic dense arithmetic. -/
setup_benchmark runCoprimeGcd n => n * n
  with prep := prepCoprime
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048,
      4096, 8192, 16384]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.5
  }

/- Brown image gcds and candidate divisions are quadratic in ambient degree;
the 8-bit family varies only degree. -/
setup_benchmark runDense8 n => n * n
  with prep := prepDense8
  where {
    paramSchedule := .custom #[16, 32, 64, 128, 256, 512, 1024, 2048,
      4096]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.5
  }

/- The coefficient width is fixed at 256 bits, so the scientific scaling axis
remains the quadratic polynomial degree. -/
setup_benchmark runDense256 n => n * n
  with prep := prepDense256
  where {
    paramSchedule := .custom #[16, 32, 64, 128, 256, 512, 1024, 2048,
      4096]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.5
    slopeTolerance := 0.3
  }

/- Degree is fixed and the parameter is coefficient bit width. The integral
PRS recurrence performs a fixed number of big-integer operations whose limb
cost is represented by `b * sqrt b` on the GMP Karatsuba-range ladder. -/
setup_benchmark runSwellPrs bits => bits * Nat.sqrt bits
  with prep := prepSwell
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048,
      4096, 8192, 16384, 32768]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.25
  }

/- The squarefree input has `n + 2` linear factors. Polynomial multiplication
and the derivative gcd are quadratic in the resulting degree. -/
setup_benchmark runSqfFast n => n * n
  with prep := prepSquarefree
  where {
    paramSchedule := .custom #[2, 4, 8, 16, 32, 64, 128, 256, 512,
      1024, 2048]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.55
    slopeTolerance := 0.2
  }

/- Denominator clearing is linear and the integer gcd dominates at quadratic
degree cost for the fixed 101/103 denominators. -/
setup_benchmark runRatGcd n => n * n
  with prep := prepRational
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048,
      4096]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.45
  }

def leanCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 10.0, warmupFirstIter := true,
    minTotalSeconds := 0.2 }

def flintCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 10.0, warmupFirstIter := true,
    minTotalSeconds := 0.2 }

setup_fixed_benchmark runFlintOverhead where flintCompareConfig

setup_fixed_benchmark runLeanGenericCoprime16 where leanCompareConfig
setup_fixed_benchmark runRationalCoprime16 where leanCompareConfig
setup_fixed_benchmark runLeanGenericCoprime32 where leanCompareConfig
setup_fixed_benchmark runRationalCoprime32 where leanCompareConfig
setup_fixed_benchmark runLeanCoprime64 where leanCompareConfig
setup_fixed_benchmark runFlintCoprime64 where flintCompareConfig
setup_fixed_benchmark runLeanGenericCoprime64 where leanCompareConfig
setup_fixed_benchmark runRationalCoprime64 where leanCompareConfig
setup_fixed_benchmark runLeanCoprime128 where leanCompareConfig
setup_fixed_benchmark runFlintCoprime128 where flintCompareConfig
setup_fixed_benchmark runLeanCoprime256 where leanCompareConfig
setup_fixed_benchmark runFlintCoprime256 where flintCompareConfig
setup_fixed_benchmark runLeanCoprime512 where leanCompareConfig
setup_fixed_benchmark runFlintCoprime512 where flintCompareConfig

setup_fixed_benchmark runLeanGenericDense8_16 where leanCompareConfig
setup_fixed_benchmark runRationalDense8_16 where leanCompareConfig
setup_fixed_benchmark runLeanGenericDense8_32 where leanCompareConfig
setup_fixed_benchmark runRationalDense8_32 where leanCompareConfig
setup_fixed_benchmark runLeanDense8_64 where leanCompareConfig
setup_fixed_benchmark runFlintDense8_64 where flintCompareConfig
setup_fixed_benchmark runLeanGenericDense8_64 where leanCompareConfig
setup_fixed_benchmark runRationalDense8_64 where leanCompareConfig
setup_fixed_benchmark runLeanDense8_128 where leanCompareConfig
setup_fixed_benchmark runFlintDense8_128 where flintCompareConfig
setup_fixed_benchmark runLeanGenericDense8_128 where leanCompareConfig
setup_fixed_benchmark runRationalDense8_128 where leanCompareConfig
setup_fixed_benchmark runLeanDense8_256 where leanCompareConfig
setup_fixed_benchmark runFlintDense8_256 where flintCompareConfig
setup_fixed_benchmark runLeanDense8_512 where leanCompareConfig
setup_fixed_benchmark runFlintDense8_512 where flintCompareConfig

setup_fixed_benchmark runLeanGenericDense256_16 where leanCompareConfig
setup_fixed_benchmark runRationalDense256_16 where leanCompareConfig
setup_fixed_benchmark runLeanGenericDense256_32 where leanCompareConfig
setup_fixed_benchmark runRationalDense256_32 where leanCompareConfig
setup_fixed_benchmark runLeanDense256_64 where leanCompareConfig
setup_fixed_benchmark runFlintDense256_64 where flintCompareConfig
setup_fixed_benchmark runLeanDense256_128 where leanCompareConfig
setup_fixed_benchmark runFlintDense256_128 where flintCompareConfig
setup_fixed_benchmark runLeanDense256_256 where leanCompareConfig
setup_fixed_benchmark runFlintDense256_256 where flintCompareConfig
setup_fixed_benchmark runLeanDense256_512 where leanCompareConfig
setup_fixed_benchmark runFlintDense256_512 where flintCompareConfig

setup_fixed_benchmark runLeanSwell512 where leanCompareConfig
setup_fixed_benchmark runRationalSwell512 where leanCompareConfig

setup_fixed_benchmark runFastSqf2 where leanCompareConfig
setup_fixed_benchmark runRationalSqf2 where leanCompareConfig
setup_fixed_benchmark runFastSqf4 where leanCompareConfig
setup_fixed_benchmark runRationalSqf4 where leanCompareConfig
setup_fixed_benchmark runFastSqf8 where leanCompareConfig
setup_fixed_benchmark runRationalSqf8 where leanCompareConfig
setup_fixed_benchmark runFastSqf16 where leanCompareConfig
setup_fixed_benchmark runRationalSqf16 where leanCompareConfig
setup_fixed_benchmark runFastSqf32 where leanCompareConfig
setup_fixed_benchmark runRationalSqf32 where leanCompareConfig
setup_fixed_benchmark runFastSqf64 where leanCompareConfig
setup_fixed_benchmark runRationalSqf64 where leanCompareConfig
setup_fixed_benchmark runFastSqf128 where leanCompareConfig
setup_fixed_benchmark runRationalSqf128 where leanCompareConfig

end Hex.PolyZGcdBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
