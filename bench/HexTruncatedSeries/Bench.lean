/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexTruncatedSeries
import LeanBench

/-!
Scientific benchmark registrations for fixed-precision truncated series.

Input construction is hoisted into `prep`.  Multiplication establishes the
schoolbook baseline; inverse is registered beside the direct coefficient
recurrence; composition registers Horner beside Brent--Kung; and reversion
registers Newton beside Lagrange.  The paired registrations let scheduled
runs enforce the SPEC's internal ratio checks without conflating them with the
informational FLINT comparison.
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

setup_benchmark runMulInt n => n * n
  with prep := prepMulInt
  where {
    paramFloor := 8
    paramCeiling := 4096
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runMulRat n => n * n
  with prep := prepMulRat
  where {
    paramFloor := 8
    paramCeiling := 4096
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runInverseNewton n => n * n
  with prep := prepInverse
  where {
    paramFloor := 8
    paramCeiling := 4096
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runInverseRecurrence n => n * n
  with prep := prepInverse
  where {
    paramFloor := 8
    paramCeiling := 4096
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runExp n => n * n
  with prep := prepExpLog
  where {
    paramFloor := 8
    paramCeiling := 1024
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runLog n => n * n
  with prep := prepExpLog
  where {
    paramFloor := 8
    paramCeiling := 1024
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runSqrt n => n * n
  with prep := prepSqrt
  where {
    paramFloor := 8
    paramCeiling := 1024
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runCompHorner n => n * n * n
  with prep := prepComposition
  where {
    paramFloor := 8
    paramCeiling := 512
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runCompBrentKung n => n * n * Nat.sqrt n
  with prep := prepComposition
  where {
    paramFloor := 8
    paramCeiling := 512
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runRevertNewton n => n * n * Nat.sqrt n * Nat.log2 (n + 1)
  with prep := prepReversion
  where {
    paramFloor := 8
    paramCeiling := 512
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runRevertLagrange n => n * n * n
  with prep := prepReversion
  where {
    paramFloor := 8
    paramCeiling := 512
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end Hex.TSeriesBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
