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

/-! Scheduled-only FLINT ladders. Each operation has enough shared rungs to
show the ratio trend after filtering out the persistent driver's framing
floor. The parametric registrations below remain the scientific internal
complexity ladders. -/

def runInverseNewton32 : Unit → IO UInt64 := runFixed runInverseNewton (prepInverse 32)
def runFlintInverse32 : Unit → IO UInt64 := runFlintFixed runFlintInverse (prepInverse 32)
def runInverseNewton64 : Unit → IO UInt64 := runFixed runInverseNewton (prepInverse 64)
def runFlintInverse64 : Unit → IO UInt64 := runFlintFixed runFlintInverse (prepInverse 64)
def runInverseNewton128 : Unit → IO UInt64 := runFixed runInverseNewton (prepInverse 128)
def runFlintInverse128 : Unit → IO UInt64 := runFlintFixed runFlintInverse (prepInverse 128)
def runInverseNewton256 : Unit → IO UInt64 := runFixed runInverseNewton (prepInverse 256)
def runFlintInverse256 : Unit → IO UInt64 := runFlintFixed runFlintInverse (prepInverse 256)
def runInverseNewton512 : Unit → IO UInt64 := runFixed runInverseNewton (prepInverse 512)
def runFlintInverse512 : Unit → IO UInt64 := runFlintFixed runFlintInverse (prepInverse 512)
def runInverseNewton1024 : Unit → IO UInt64 := runFixed runInverseNewton (prepInverse 1024)
def runFlintInverse1024 : Unit → IO UInt64 := runFlintFixed runFlintInverse (prepInverse 1024)

def runExp16 : Unit → IO UInt64 := runFixed runExp (prepExpLog 16)
def runFlintExp16 : Unit → IO UInt64 := runFlintFixed runFlintExp (prepExpLog 16)
def runExp32 : Unit → IO UInt64 := runFixed runExp (prepExpLog 32)
def runFlintExp32 : Unit → IO UInt64 := runFlintFixed runFlintExp (prepExpLog 32)
def runExp64 : Unit → IO UInt64 := runFixed runExp (prepExpLog 64)
def runFlintExp64 : Unit → IO UInt64 := runFlintFixed runFlintExp (prepExpLog 64)
def runExp128 : Unit → IO UInt64 := runFixed runExp (prepExpLog 128)
def runFlintExp128 : Unit → IO UInt64 := runFlintFixed runFlintExp (prepExpLog 128)
def runExp256 : Unit → IO UInt64 := runFixed runExp (prepExpLog 256)
def runFlintExp256 : Unit → IO UInt64 := runFlintFixed runFlintExp (prepExpLog 256)

def runLog16 : Unit → IO UInt64 := runFixed runLog (prepExpLog 16)
def runFlintLog16 : Unit → IO UInt64 := runFlintFixed runFlintLog (prepExpLog 16)
def runLog32 : Unit → IO UInt64 := runFixed runLog (prepExpLog 32)
def runFlintLog32 : Unit → IO UInt64 := runFlintFixed runFlintLog (prepExpLog 32)
def runLog64 : Unit → IO UInt64 := runFixed runLog (prepExpLog 64)
def runFlintLog64 : Unit → IO UInt64 := runFlintFixed runFlintLog (prepExpLog 64)
def runLog128 : Unit → IO UInt64 := runFixed runLog (prepExpLog 128)
def runFlintLog128 : Unit → IO UInt64 := runFlintFixed runFlintLog (prepExpLog 128)
def runLog256 : Unit → IO UInt64 := runFixed runLog (prepExpLog 256)
def runFlintLog256 : Unit → IO UInt64 := runFlintFixed runFlintLog (prepExpLog 256)

def runSqrt16 : Unit → IO UInt64 := runFixed runSqrt (prepSqrt 16)
def runFlintSqrt16 : Unit → IO UInt64 := runFlintFixed runFlintSqrt (prepSqrt 16)
def runSqrt32 : Unit → IO UInt64 := runFixed runSqrt (prepSqrt 32)
def runFlintSqrt32 : Unit → IO UInt64 := runFlintFixed runFlintSqrt (prepSqrt 32)
def runSqrt64 : Unit → IO UInt64 := runFixed runSqrt (prepSqrt 64)
def runFlintSqrt64 : Unit → IO UInt64 := runFlintFixed runFlintSqrt (prepSqrt 64)
def runSqrt128 : Unit → IO UInt64 := runFixed runSqrt (prepSqrt 128)
def runFlintSqrt128 : Unit → IO UInt64 := runFlintFixed runFlintSqrt (prepSqrt 128)
def runSqrt256 : Unit → IO UInt64 := runFixed runSqrt (prepSqrt 256)
def runFlintSqrt256 : Unit → IO UInt64 := runFlintFixed runFlintSqrt (prepSqrt 256)

def runCompBrentKung8 : Unit → IO UInt64 := runFixed runCompBrentKung (prepComposition 8)
def runFlintComposition8 : Unit → IO UInt64 :=
  runFlintFixed runFlintComposition (prepComposition 8)
def runCompBrentKung16 : Unit → IO UInt64 := runFixed runCompBrentKung (prepComposition 16)
def runFlintComposition16 : Unit → IO UInt64 :=
  runFlintFixed runFlintComposition (prepComposition 16)
def runCompBrentKung32 : Unit → IO UInt64 := runFixed runCompBrentKung (prepComposition 32)
def runFlintComposition32 : Unit → IO UInt64 :=
  runFlintFixed runFlintComposition (prepComposition 32)
def runCompBrentKung64 : Unit → IO UInt64 := runFixed runCompBrentKung (prepComposition 64)
def runFlintComposition64 : Unit → IO UInt64 :=
  runFlintFixed runFlintComposition (prepComposition 64)
def runCompBrentKung128 : Unit → IO UInt64 := runFixed runCompBrentKung (prepComposition 128)
def runFlintComposition128 : Unit → IO UInt64 :=
  runFlintFixed runFlintComposition (prepComposition 128)

def runRevertNewton8 : Unit → IO UInt64 := runFixed runRevertNewton (prepReversion 8)
def runFlintReversion8 : Unit → IO UInt64 := runFlintFixed runFlintReversion (prepReversion 8)
def runRevertNewton16 : Unit → IO UInt64 := runFixed runRevertNewton (prepReversion 16)
def runFlintReversion16 : Unit → IO UInt64 := runFlintFixed runFlintReversion (prepReversion 16)
def runRevertNewton32 : Unit → IO UInt64 := runFixed runRevertNewton (prepReversion 32)
def runFlintReversion32 : Unit → IO UInt64 := runFlintFixed runFlintReversion (prepReversion 32)
def runRevertNewton64 : Unit → IO UInt64 := runFixed runRevertNewton (prepReversion 64)
def runFlintReversion64 : Unit → IO UInt64 := runFlintFixed runFlintReversion (prepReversion 64)
def runRevertNewton128 : Unit → IO UInt64 := runFixed runRevertNewton (prepReversion 128)
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

/- Cost model: exponential Newton refinement performs `O(n²)` coefficient
operations. On the `exp x` rational fixture, factorial denominators have
`Θ(n log n)` bits; two logarithmic factors are the repository's wallclock
normalization for the repeated arbitrary-precision numerator/denominator
work, without changing the coefficient-operation bound in the SPEC. Running
each inner logarithm at full precision would add another logarithmic factor,
so the normalized ratio would still grow rather than settle. -/
setup_benchmark runExp n => n ^ 2 * (Nat.log2 (n + 1) + 1) ^ 2
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

/- Cost model: square-root Newton refinement performs `O(n²)` coefficient
operations. The exact binomial coefficients in `sqrt (1 + x)` grow beyond
immediate rationals along this ladder, so one logarithmic factor records the
measured limb-growth wallclock cost separately from that operation count. -/
setup_benchmark runSqrt n => n ^ 2 * (Nat.log2 (n + 1) + 1)
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
  { repeats := 5, maxSecondsPerCall := 12.0, minTotalSeconds := 0.2,
    tags := #["flint-series"] }

def flintCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 12.0, minTotalSeconds := 0.2,
    warmupFirstIter := true, tags := #["flint-series"] }

setup_fixed_benchmark runFlintSeriesOverhead where
  { flintCompareConfig with expectedHash := some 0x0 }

setup_fixed_benchmark runInverseNewton32 where
  { leanCompareConfig with expectedHash := some 0xf83985833c82a500 }
setup_fixed_benchmark runFlintInverse32 where
  { flintCompareConfig with expectedHash := some 0xf83985833c82a500 }
setup_fixed_benchmark runInverseNewton64 where
  { leanCompareConfig with expectedHash := some 0xb89356db72c3ea00 }
setup_fixed_benchmark runFlintInverse64 where
  { flintCompareConfig with expectedHash := some 0xb89356db72c3ea00 }
setup_fixed_benchmark runInverseNewton128 where
  { leanCompareConfig with expectedHash := some 0xc4b79683cd425c00 }
setup_fixed_benchmark runFlintInverse128 where
  { flintCompareConfig with expectedHash := some 0xc4b79683cd425c00 }
setup_fixed_benchmark runInverseNewton256 where
  { leanCompareConfig with expectedHash := some 0x0ffe9490134bd800 }
setup_fixed_benchmark runFlintInverse256 where
  { flintCompareConfig with expectedHash := some 0x0ffe9490134bd800 }
setup_fixed_benchmark runInverseNewton512 where
  { leanCompareConfig with expectedHash := some 0x0100406f0dfcd000 }
setup_fixed_benchmark runFlintInverse512 where
  { flintCompareConfig with expectedHash := some 0x0100406f0dfcd000 }
setup_fixed_benchmark runInverseNewton1024 where
  { leanCompareConfig with expectedHash := some 0x346b8ae7554ba000 }
setup_fixed_benchmark runFlintInverse1024 where
  { flintCompareConfig with expectedHash := some 0x346b8ae7554ba000 }

setup_fixed_benchmark runExp16 where
  { leanCompareConfig with expectedHash := some 0x89a65ce036888559 }
setup_fixed_benchmark runFlintExp16 where
  { flintCompareConfig with expectedHash := some 0x89a65ce036888559 }
setup_fixed_benchmark runExp32 where
  { leanCompareConfig with expectedHash := some 0x9c303149750845f3 }
setup_fixed_benchmark runFlintExp32 where
  { flintCompareConfig with expectedHash := some 0x9c303149750845f3 }
setup_fixed_benchmark runExp64 where
  { leanCompareConfig with expectedHash := some 0x4a2979405bbf05e7 }
setup_fixed_benchmark runFlintExp64 where
  { flintCompareConfig with expectedHash := some 0x4a2979405bbf05e7 }
setup_fixed_benchmark runExp128 where
  { leanCompareConfig with expectedHash := some 0x5ba20a7eb78edf83 }
setup_fixed_benchmark runFlintExp128 where
  { flintCompareConfig with expectedHash := some 0x5ba20a7eb78edf83 }
setup_fixed_benchmark runExp256 where
  { leanCompareConfig with expectedHash := some 0x069e516a33ede883 }
setup_fixed_benchmark runFlintExp256 where
  { flintCompareConfig with expectedHash := some 0x069e516a33ede883 }

setup_fixed_benchmark runLog16 where
  { leanCompareConfig with expectedHash := some 0xa572eff49e0b3afa }
setup_fixed_benchmark runFlintLog16 where
  { flintCompareConfig with expectedHash := some 0xa572eff49e0b3afa }
setup_fixed_benchmark runLog32 where
  { leanCompareConfig with expectedHash := some 0xc3bc8c91696b0f51 }
setup_fixed_benchmark runFlintLog32 where
  { flintCompareConfig with expectedHash := some 0xc3bc8c91696b0f51 }
setup_fixed_benchmark runLog64 where
  { leanCompareConfig with expectedHash := some 0x6a3b024a295ac34c }
setup_fixed_benchmark runFlintLog64 where
  { flintCompareConfig with expectedHash := some 0x6a3b024a295ac34c }
setup_fixed_benchmark runLog128 where
  { leanCompareConfig with expectedHash := some 0x43551f34659a7816 }
setup_fixed_benchmark runFlintLog128 where
  { flintCompareConfig with expectedHash := some 0x43551f34659a7816 }
setup_fixed_benchmark runLog256 where
  { leanCompareConfig with expectedHash := some 0x2675aa116b00ad7b }
setup_fixed_benchmark runFlintLog256 where
  { flintCompareConfig with expectedHash := some 0x2675aa116b00ad7b }

setup_fixed_benchmark runSqrt16 where
  { leanCompareConfig with expectedHash := some 0xe8b590030f4a6cd9 }
setup_fixed_benchmark runFlintSqrt16 where
  { flintCompareConfig with expectedHash := some 0xe8b590030f4a6cd9 }
setup_fixed_benchmark runSqrt32 where
  { leanCompareConfig with expectedHash := some 0xff0a8b609ca1628c }
setup_fixed_benchmark runFlintSqrt32 where
  { flintCompareConfig with expectedHash := some 0xff0a8b609ca1628c }
setup_fixed_benchmark runSqrt64 where
  { leanCompareConfig with expectedHash := some 0x2b9d3bf6d2984fd6 }
setup_fixed_benchmark runFlintSqrt64 where
  { flintCompareConfig with expectedHash := some 0x2b9d3bf6d2984fd6 }
setup_fixed_benchmark runSqrt128 where
  { leanCompareConfig with expectedHash := some 0xbb3b74deb5d64da9 }
setup_fixed_benchmark runFlintSqrt128 where
  { flintCompareConfig with expectedHash := some 0xbb3b74deb5d64da9 }
setup_fixed_benchmark runSqrt256 where
  { leanCompareConfig with expectedHash := some 0xd8b09a4d5518bc09 }
setup_fixed_benchmark runFlintSqrt256 where
  { flintCompareConfig with expectedHash := some 0xd8b09a4d5518bc09 }

setup_fixed_benchmark runCompBrentKung8 where
  { leanCompareConfig with expectedHash := some 0x8b6a4e2379341be3 }
setup_fixed_benchmark runFlintComposition8 where
  { flintCompareConfig with expectedHash := some 0x8b6a4e2379341be3 }
setup_fixed_benchmark runCompBrentKung16 where
  { leanCompareConfig with expectedHash := some 0x6de141f809e6a9e6 }
setup_fixed_benchmark runFlintComposition16 where
  { flintCompareConfig with expectedHash := some 0x6de141f809e6a9e6 }
setup_fixed_benchmark runCompBrentKung32 where
  { leanCompareConfig with expectedHash := some 0x2552768b42a68b6a }
setup_fixed_benchmark runFlintComposition32 where
  { flintCompareConfig with expectedHash := some 0x2552768b42a68b6a }
setup_fixed_benchmark runCompBrentKung64 where
  { leanCompareConfig with expectedHash := some 0xdaf38d401b898152 }
setup_fixed_benchmark runFlintComposition64 where
  { flintCompareConfig with expectedHash := some 0xdaf38d401b898152 }
setup_fixed_benchmark runCompBrentKung128 where
  { leanCompareConfig with expectedHash := some 0x79bc2ec690dc96e7 }
setup_fixed_benchmark runFlintComposition128 where
  { flintCompareConfig with expectedHash := some 0x79bc2ec690dc96e7 }

setup_fixed_benchmark runRevertNewton8 where
  { leanCompareConfig with expectedHash := some 0xd82bbe20935bf27e }
setup_fixed_benchmark runFlintReversion8 where
  { flintCompareConfig with expectedHash := some 0xd82bbe20935bf27e }
setup_fixed_benchmark runRevertNewton16 where
  { leanCompareConfig with expectedHash := some 0x7260ea3b2c547680 }
setup_fixed_benchmark runFlintReversion16 where
  { flintCompareConfig with expectedHash := some 0x7260ea3b2c547680 }
setup_fixed_benchmark runRevertNewton32 where
  { leanCompareConfig with expectedHash := some 0x1085ce620dff4e6d }
setup_fixed_benchmark runFlintReversion32 where
  { flintCompareConfig with expectedHash := some 0x1085ce620dff4e6d }
setup_fixed_benchmark runRevertNewton64 where
  { leanCompareConfig with expectedHash := some 0xb3d5335a9c8e2c39 }
setup_fixed_benchmark runFlintReversion64 where
  { flintCompareConfig with expectedHash := some 0xb3d5335a9c8e2c39 }
setup_fixed_benchmark runRevertNewton128 where
  { leanCompareConfig with expectedHash := some 0xf6179a69798169bb }
setup_fixed_benchmark runFlintReversion128 where
  { flintCompareConfig with expectedHash := some 0xf6179a69798169bb }

end Hex.TSeriesBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
