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

structure DivisionInput where
  dividend : DensePoly Rat
  divisor : DensePoly Rat

instance : Hashable DivisionInput where
  hash input := mixHash (hash input.dividend.toArray) (hash input.divisor.toArray)

def prepDivision (n : Nat) : DivisionInput :=
  { dividend := ofList ((List.range (2 * n + 1)).map fun i => (coeff i 31 : Rat))
    divisor := ofList (((List.range n).map fun i => (coeff i 47 : Rat)) ++ [1]) }

private def checksumRat (p : DensePoly Rat) : UInt64 :=
  p.toArray.foldl (fun acc x => mixHash acc (hash x)) 0

private def checksumDiv (qr : DensePoly Rat × DensePoly Rat) : UInt64 :=
  mixHash (checksumRat qr.1) (checksumRat qr.2)

def runLongDivision (input : DivisionInput) : UInt64 :=
  checksumDiv (divMod input.dividend input.divisor)

def runNewtonDivision (input : DivisionInput) : UInt64 :=
  checksumDiv (divModWith (karatsubaPlan 32) input.dividend input.divisor)

structure ProductTreeInput where
  leaves : Array (DensePoly Int)

instance : Hashable ProductTreeInput where
  hash input := input.leaves.foldl
    (fun acc p => mixHash acc (hash p.toArray)) 0

def prepProductTree (n : Nat) : ProductTreeInput :=
  { leaves := (List.range n).map (fun i => ofList [-(coeff i 59), 1]) |>.toArray }

def runProductTree (input : ProductTreeInput) : UInt64 :=
  checksum (ProductTree.build (karatsubaPlan 32) input.leaves).root

structure MultipointInput where
  plan : EvalPlan Int
  polynomial : DensePoly Int

instance : Hashable MultipointInput where
  hash input := mixHash (hash input.plan.points) (hash input.polynomial.toArray)

def prepMultipoint (n : Nat) : MultipointInput :=
  let points := (List.range n).map (fun i => Int.ofNat i - Int.ofNat (n / 2)) |>.toArray
  { plan := EvalPlan.build (karatsubaPlan 32) points
    polynomial := ofList ((List.range n).map fun i => coeff i 71) }

private def checksumValues (values : Array Int) : UInt64 :=
  values.foldl (fun acc value => mixHash acc (hash value)) 0

def runDirectEval (input : MultipointInput) : UInt64 :=
  checksumValues (input.plan.points.map (input.polynomial.eval ·))

def runMultipointEval (input : MultipointInput) : UInt64 :=
  checksumValues (input.plan.eval input.polynomial)

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

/- The long-division comparator eliminates one leading coefficient at a time
and updates a linear suffix, giving a quadratic coefficient-operation model. -/
setup_benchmark runLongDivision n => n ^ 2
  with prep := prepDivision
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "long", "cold"]
  }

/- Cost model: a cold Newton call includes reciprocal construction and three clipped
Karatsuba products.  Doubling is geometric, so the balanced model remains
`Θ(M(n))`, represented by the Karatsuba-range integer surrogate. -/
setup_benchmark runNewtonDivision n => n * (Nat.sqrt n)
  with prep := prepDivision
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "newton", "cold"]
  }

/- A balanced product tree performs one multiplication per internal node over
geometrically growing degrees, for `O(M(n) log n)` total work. The integer
surrogate retains the logarithmic level count without assuming a particular
coefficient-kernel exponent. -/
setup_benchmark runProductTree n => n * (Nat.log2 n + 1)
  with prep := prepProductTree
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["product-tree", "karatsuba", "cold"]
  }

/- Direct Horner evaluation visits all `n` coefficients independently at all
`n` points, giving quadratic (`Θ(n²)`) coefficient operations. -/
setup_benchmark runDirectEval n => n ^ 2
  with prep := prepMultipoint
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multipoint", "horner", "reused-plan"]
  }

/- With products and reciprocals prepared outside the timed call, the balanced
remainder tree costs `O(M(n) log n)`. -/
setup_benchmark runMultipointEval n => n * (Nat.sqrt n) * (Nat.log2 n + 1)
  with prep := prepMultipoint
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multipoint", "remainder-tree", "reused-plan"]
  }

end Hex.PolyFastBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
