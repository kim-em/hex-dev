/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyFast
import LeanBench

/-!
Scientific benchmark registrations for the generic multiplication crossover.
Input preparation is excluded from timing, and every target consumes its
result through a coefficient hash.
-/

namespace Hex.PolyFastBench

open Hex Hex.DensePoly

structure Binary where
  left : DensePoly Int
  right : DensePoly Int

instance : Hashable Binary where
  hash input := mixHash (hash input.left.toArray) (hash input.right.toArray)

private def coeff (i salt : Nat) : Int :=
  Int.ofNat (((i + 3) * (salt + 11)) % 101 + 1) - 50

def prepBalanced (n : Nat) : Binary :=
  { left := ofList ((List.range n).map fun i => coeff i 3)
    right := ofList ((List.range n).map fun i => coeff i 19) }

def prepSkew (n : Nat) : Binary :=
  { left := ofList ((List.range (64 * n)).map fun i => coeff i 5)
    right := ofList ((List.range n).map fun i => coeff i 23) }

private def checksum (p : DensePoly Int) : UInt64 :=
  p.toArray.foldl (fun acc x => mixHash acc (hash x)) 0

def runSchoolbook (input : Binary) : UInt64 :=
  checksum (mulWith schoolbookPlan input.left input.right)

def runKaratsuba (input : Binary) : UInt64 :=
  checksum (mulWith (karatsubaPlan 32) input.left input.right)

def runKaratsubaSkew (input : Binary) : UInt64 :=
  checksum (mulWith (karatsubaPlan 32) input.left input.right)

def runKaratsubaSquare (input : Binary) : UInt64 :=
  checksum (squareWith (karatsubaPlan 32) input.left)

/- Cost model: a balanced length-`n` schoolbook convolution evaluates one
coefficient product for each input pair, hence `n²` ring multiplications. -/
setup_benchmark runSchoolbook n => n ^ 2
  with prep := prepBalanced
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "schoolbook", "balanced"]
  }

/- Cost model: balanced Karatsuba satisfies `T(n) = 3T(n/2) + O(n)`, hence
`T(n) = Θ(n^(log₂ 3))`; `n * sqrt n` is its integer-valued surrogate.
The nearby 31/32/33 rungs expose the fixed cutoff. -/
setup_benchmark runKaratsuba n => n * (Nat.sqrt n)
  with prep := prepBalanced
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "balanced"]
  }

/- Cost model: specialized squaring performs three recursive squares plus
linear combination work, so it obeys the same `Θ(n^(log₂ 3))` recurrence;
`n * sqrt n` is the integer-valued Karatsuba-range surrogate. -/
setup_benchmark runKaratsubaSquare n => n * (Nat.sqrt n)
  with prep := prepBalanced
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "square"]
  }

/- Cost model: the 64:1 dispatcher partitions the long operand into 64
length-`n` blocks.  That constant factor preserves the balanced Karatsuba
bound `Θ(n^(log₂ 3))`, represented by the `n * sqrt n` surrogate. -/
setup_benchmark runKaratsubaSkew n => n * (Nat.sqrt n)
  with prep := prepSkew
  where {
    paramFloor := 4
    paramCeiling := 256
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "ratio-64"]
  }

end Hex.PolyFastBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
