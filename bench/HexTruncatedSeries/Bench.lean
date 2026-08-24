/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexTruncatedSeries
import Hex.BenchOracle.Flint
import LeanBench

/-!
Scientific benchmark registrations for fixed-precision truncated series.

Input construction is hoisted into `prep`.  Multiplication establishes the
schoolbook baseline; inverse is registered beside the direct coefficient
recurrence; composition registers Horner beside Brent--Kung; and reversion
registers Newton beside Lagrange.  The paired registrations let scheduled
runs enforce the SPEC's internal ratio checks without conflating them with the
informational FLINT comparison.

The FLINT arms use python-flint's `fmpq_series` wrapper around the named
`fmpq_poly_*_series` kernels.  They are fixed, scheduled-only registrations:
one representative shared input per operation, driven through the repository's
persistent subprocess.  `warmupFirstIter` starts that process before timing;
subsequent auto-tuned calls reuse it.  `runFlintSeriesOverhead` records the
steady-state JSON framing floor for the headline report.
-/

namespace Hex.TSeriesBench

open Hex Hex.TSeries
open scoped Hex

private def checksum [Hashable R] (a : TSeries R n) : UInt64 :=
  a.coeffs.toArray.foldl (fun acc x => mixHash acc (hash x)) 0

private def checksumArray [Hashable R] (a : Array R) : UInt64 :=
  a.foldl (fun acc x => mixHash acc (hash x)) 0

structure IntBinary where
  n : Nat
  left : TSeries Int n
  right : TSeries Int n

structure RatBinary where
  n : Nat
  left : TSeries Rat n
  right : TSeries Rat n

structure RatUnary where
  n : Nat
  value : TSeries Rat n

instance : Hashable IntBinary where
  hash input := mixHash (hash input.n)
    (mixHash (hash input.left.coeffs.toArray) (hash input.right.coeffs.toArray))

instance : Hashable RatBinary where
  hash input := mixHash (hash input.n)
    (mixHash (hash input.left.coeffs.toArray) (hash input.right.coeffs.toArray))

instance : Hashable RatUnary where
  hash input := mixHash (hash input.n) (hash input.value.coeffs.toArray)

private def intCoeff (n i salt : Nat) : Int :=
  Int.ofNat (((i + 1) * (salt + 11) + n * 17) % 101 + 1)

private def ratCoeff (n i salt : Nat) : Rat :=
  Rat.ofInt (intCoeff n i salt)

def prepMulInt (n : Nat) : IntBinary :=
  { n
    left := ofFn fun i => intCoeff n i 3
    right := ofFn fun i => intCoeff n i 19 }

def prepMulRat (n : Nat) : RatBinary :=
  { n
    left := ofFn fun i => ratCoeff n i 5
    right := ofFn fun i => ratCoeff n i 23 }

def prepInverse (n : Nat) : RatUnary :=
  { n
    value := ofFn fun i => if i = 0 then 1 else if i = 1 then -1 else 0 }

def prepExpLog (n : Nat) : RatUnary :=
  { n
    value := ofFn fun i => if i = 1 then 1 else 0 }

def prepSqrt (n : Nat) : RatUnary :=
  { n
    value := ofFn fun i => if i = 0 ∨ i = 1 then 1 else 0 }

def prepComposition (n : Nat) : RatBinary :=
  { n
    left := ofFn fun _ => 1
    right := ofFn fun i => if i = 1 ∨ i = 2 then 1 else 0 }

def prepReversion (n : Nat) : RatUnary :=
  { n
    value := ofFn fun i => if i = 1 ∨ i = 2 then 1 else 0 }

def runMulInt (input : IntBinary) : UInt64 :=
  checksum (input.left * input.right)

def runMulRat (input : RatBinary) : UInt64 :=
  checksum (input.left * input.right)

def runInverseNewton (input : RatUnary) : UInt64 :=
  checksum (invOfUnit input.value 1)

/-- Direct `O(n²)` coefficient recurrence used as the inversion baseline. -/
def runInverseRecurrence (input : RatUnary) : UInt64 :=
  let u := (input.value.coeff 0)⁻¹
  let coeffs : Array Rat := (List.range input.n).foldl (fun out i =>
    let next : Rat := if i = 0 then u else
      -u * ((List.range i).foldl (fun acc j =>
        acc + input.value.coeff (i - j) * out[j]!) 0)
    out.push next) (#[] : Array Rat)
  checksumArray coeffs

def runExp (input : RatUnary) : UInt64 :=
  checksum (exp input.value)

def runLog (input : RatUnary) : UInt64 :=
  checksum (log (1 + input.value))

def runSqrt (input : RatUnary) : UInt64 :=
  checksum (sqrtOfRoot input.value 1 (1 / 2))

def runCompHorner (input : RatBinary) : UInt64 :=
  checksum (compHorner input.left input.right)

def runCompBrentKung (input : RatBinary) : UInt64 :=
  checksum (compBrentKung input.left input.right)

def runRevertNewton (input : RatUnary) : UInt64 :=
  checksum (revOfUnit input.value 1)

def runRevertLagrange (input : RatUnary) : UInt64 :=
  checksum (revLagrange input.value 1)

private def ratListJson (xs : List Rat) : Lean.Json :=
  let nums := xs.map fun q => Lean.Json.num (Lean.JsonNumber.fromInt q.num)
  let dens := xs.map fun q => Lean.Json.num (Lean.JsonNumber.fromNat q.den)
  Lean.Json.mkObj
    [("num", Lean.Json.arr nums.toArray), ("den", Lean.Json.arr dens.toArray)]

private def seriesJson (a : TSeries Rat n) : Lean.Json :=
  ratListJson a.coeffs.toArray.toList

private def jsonError (context : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => return value
  | .error msg => throw <| IO.userError s!"{context}: {msg}"

private def jsonToRats (value : Lean.Json) : IO (Array Rat) := do
  let numsValue ← jsonError "FLINT rational result missing num"
    (value.getObjVal? "num")
  let densValue ← jsonError "FLINT rational result missing den"
    (value.getObjVal? "den")
  let nums ← jsonError "FLINT rational num is not an array" numsValue.getArr?
  let dens ← jsonError "FLINT rational den is not an array" densValue.getArr?
  unless nums.size = dens.size do
    throw <| IO.userError "FLINT rational numerator/denominator lengths differ"
  let mut out : Array Rat := Array.mkEmpty nums.size
  for (numValue, denValue) in nums.zip dens do
    let num ← jsonError "FLINT rational numerator is not an integer" numValue.getInt?
    let den ← jsonError "FLINT rational denominator is not a natural" denValue.getNat?
    if hden : den = 0 then
      throw <| IO.userError "FLINT rational denominator is zero"
    else
      out := out.push (Rat.normalize num den hden)
  return out

private def precisionJson (n : Nat) : Lean.Json :=
  Lean.Json.num (Lean.JsonNumber.fromNat n)

private def runFlintUnary (op : String) (input : RatUnary) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpq_series" op
    #[("precision", precisionJson input.n), ("a", seriesJson input.value)]
  return checksumArray (← jsonToRats result)

def runFlintInverse (input : RatUnary) : IO UInt64 :=
  runFlintUnary "inv" input

def runFlintExp (input : RatUnary) : IO UInt64 :=
  runFlintUnary "exp" input

def runFlintLog (input : RatUnary) : IO UInt64 :=
  runFlintUnary "log" { input with value := 1 + input.value }

def runFlintSqrt (input : RatUnary) : IO UInt64 :=
  runFlintUnary "sqrt" input

def runFlintComposition (input : RatBinary) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpq_series" "compose"
    #[("precision", precisionJson input.n),
      ("a", seriesJson input.left), ("b", seriesJson input.right)]
  return checksumArray (← jsonToRats result)

def runFlintReversion (input : RatUnary) : IO UInt64 :=
  runFlintUnary "revert" input

/-- Persistent-driver framing/dispatch calibration without series work. -/
def runFlintSeriesOverhead (_ : Unit) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpq_series" "overhead" #[]
  return checksumArray (← jsonToRats result)

private def runFixed (run : α → UInt64) (input : α) : Unit → IO UInt64 := fun _ =>
  return run input

private def runFlintFixed (run : α → IO UInt64) (input : α) : Unit → IO UInt64 := fun _ =>
  run input

/-! Representative scheduled-only FLINT pairs.  These sizes are large enough
to exercise the actual series kernels while keeping `verify` a smoke test; the
parametric registrations above remain the scientific internal ladders. -/

def runInverseNewton1024 : Unit → IO UInt64 :=
  runFixed runInverseNewton (prepInverse 1024)
def runFlintInverse1024 : Unit → IO UInt64 :=
  runFlintFixed runFlintInverse (prepInverse 1024)

def runExp256 : Unit → IO UInt64 := runFixed runExp (prepExpLog 256)
def runFlintExp256 : Unit → IO UInt64 := runFlintFixed runFlintExp (prepExpLog 256)

def runLog256 : Unit → IO UInt64 := runFixed runLog (prepExpLog 256)
def runFlintLog256 : Unit → IO UInt64 := runFlintFixed runFlintLog (prepExpLog 256)

def runSqrt256 : Unit → IO UInt64 := runFixed runSqrt (prepSqrt 256)
def runFlintSqrt256 : Unit → IO UInt64 := runFlintFixed runFlintSqrt (prepSqrt 256)

def runCompBrentKung128 : Unit → IO UInt64 :=
  runFixed runCompBrentKung (prepComposition 128)
def runFlintComposition128 : Unit → IO UInt64 :=
  runFlintFixed runFlintComposition (prepComposition 128)

def runRevertNewton128 : Unit → IO UInt64 :=
  runFixed runRevertNewton (prepReversion 128)
def runFlintReversion128 : Unit → IO UInt64 :=
  runFlintFixed runFlintReversion (prepReversion 128)

/- Cost model: schoolbook truncation computes coefficient `k` from `k + 1`
products, so summing over `k < n` gives `n(n + 1)/2 = O(n²)` integer
coefficient operations. -/
setup_benchmark runMulInt n => n ^ 2
  with prep := prepMulInt
  where {
    paramFloor := 8
    paramCeiling := 4096
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: the rational implementation has the same triangular
schoolbook convolution as the integer arm, hence `O(n²)` coefficient
operations; coefficient-size growth is measured rather than hidden here. -/
setup_benchmark runMulRat n => n ^ 2
  with prep := prepMulRat
  where {
    paramFloor := 8
    paramCeiling := 4096
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: Newton inversion doubles precision and performs a constant
number of schoolbook products at each precision.  The geometric sum
`1² + 2² + 4² + ... + n²` is `O(n²)`, dominated by the final step. -/
setup_benchmark runInverseNewton n => n ^ 2
  with prep := prepInverse
  where {
    paramFloor := 8
    paramCeiling := 4096
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: coefficient `i` folds over the preceding `i` coefficients;
the sum `1 + ... + (n - 1)` is `O(n²)` rational operations. -/
setup_benchmark runInverseRecurrence n => n ^ 2
  with prep := prepInverse
  where {
    paramFloor := 8
    paramCeiling := 4096
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: exponential Newton refinement doubles precision and each step
uses a constant number of bounded schoolbook products plus linear derivative
and integration passes, so the geometric sum is `O(n²)`. -/
setup_benchmark runExp n => n ^ 2
  with prep := prepExpLog
  where {
    paramFloor := 8
    paramCeiling := 1024
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: logarithm computes a derivative, one Newton inverse, one
schoolbook product, and an integration.  The inverse and product dominate at
`O(n²)` coefficient operations. -/
setup_benchmark runLog n => n ^ 2
  with prep := prepExpLog
  where {
    paramFloor := 8
    paramCeiling := 1024
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: square-root Newton refinement doubles precision and performs a
constant number of schoolbook products/inversions per step; the final
precision dominates the geometric sum at `O(n²)`. -/
setup_benchmark runSqrt n => n ^ 2
  with prep := prepSqrt
  where {
    paramFloor := 8
    paramCeiling := 1024
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: Horner performs `n` truncated schoolbook multiplications, each
with `O(n²)` coefficient operations, for `O(n³)` overall. -/
setup_benchmark runCompHorner n => n ^ 3
  with prep := prepComposition
  where {
    paramFloor := 8
    paramCeiling := 512
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512]
    maxSecondsPerCall := 45.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: Brent--Kung uses blocks of width `√n`; precomputing inner
powers and combining the `√n` outer blocks takes `O(√n)` truncated
schoolbook products, hence `O(n²√n)` coefficient operations. -/
setup_benchmark runCompBrentKung n => n ^ 2 * Nat.sqrt n
  with prep := prepComposition
  where {
    paramFloor := 8
    paramCeiling := 512
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512]
    maxSecondsPerCall := 15.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Bounded Newton reversion is a geometric sum of Brent--Kung compositions,
not one full composition per doubling.  The last `O(n²√n)` step dominates. -/
setup_benchmark runRevertNewton n => n ^ 2 * Nat.sqrt n
  with prep := prepReversion
  where {
    paramFloor := 8
    paramCeiling := 512
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512]
    maxSecondsPerCall := 20.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- The direct route performs `n` schoolbook products, hence `O(n³)`
coefficient operations.  Its exact rational power coefficients grow across
the ladder; the logarithmic factor is the same limb-growth wallclock proxy
used by the repository's other arbitrary-precision registrations. -/
setup_benchmark runRevertLagrange n => n ^ 3 * (Nat.log2 (n + 1) + 1)
  with prep := prepReversion
  where {
    paramFloor := 8
    paramCeiling := 512
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512]
    maxSecondsPerCall := 80.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-! # Informational FLINT comparator registrations

Each pair returns the same coefficient checksum, so `compare` also checks
cross-system agreement.  The comparator is informational and scheduled-only;
python-flint must be installed in the scheduled/release environment. -/

def leanCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 12.0, minTotalSeconds := 0.2 }

def flintCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 12.0, minTotalSeconds := 0.2,
    warmupFirstIter := true }

setup_fixed_benchmark runFlintSeriesOverhead where flintCompareConfig

setup_fixed_benchmark runInverseNewton1024 where leanCompareConfig
setup_fixed_benchmark runFlintInverse1024 where flintCompareConfig
setup_fixed_benchmark runExp256 where leanCompareConfig
setup_fixed_benchmark runFlintExp256 where flintCompareConfig
setup_fixed_benchmark runLog256 where leanCompareConfig
setup_fixed_benchmark runFlintLog256 where flintCompareConfig
setup_fixed_benchmark runSqrt256 where leanCompareConfig
setup_fixed_benchmark runFlintSqrt256 where flintCompareConfig
setup_fixed_benchmark runCompBrentKung128 where leanCompareConfig
setup_fixed_benchmark runFlintComposition128 where flintCompareConfig
setup_fixed_benchmark runRevertNewton128 where leanCompareConfig
setup_fixed_benchmark runFlintReversion128 where flintCompareConfig

end Hex.TSeriesBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
