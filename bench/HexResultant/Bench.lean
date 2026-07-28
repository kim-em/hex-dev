/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexResultant
import LeanBench

/-!
Benchmark registrations for `HexResultant`.

The four scientific families expose the public computational stages required
by the library SPEC:

* `runPseudoDiv` computes one pseudo-division with degrees `n` and `n / 2`;
* `runChain` retains the complete Brown subresultant chain;
* `runResultant` computes the resultant of two deterministic dense integer
  polynomials of equal degree `n`;
* `runDisc` computes the discriminant of the left member of the same family.

Inputs use the same seed-`0xC0FFEE` bounded-coefficient LCG family as the
external fixtures, with every leading coefficient forced nonzero. There is no
in-process comparator in this executable: Mathlib's resultant is
noncomputable, while exact FLINT/PARI value checking belongs to conformance.
FLINT's separately timed comparable surface belongs in the Phase-4 report.
-/

namespace Hex.ResultantBench

open Hex.DensePoly

instance : Hashable (DensePoly Int) where
  hash p := hash p.toArray

/-- A prepared pair of dense degree-`n` integer polynomials. -/
structure Input where
  left : DensePoly Int
  right : DensePoly Int
  deriving Hashable

private def initialSeed : UInt64 :=
  0xC0FFEE

private def nextSeed (seed : UInt64) : UInt64 :=
  seed * 6364136223846793005 + 1442695040888963407

private structure PolyState where
  seed : UInt64
  coeffs : Array Int

private def generatedPoly (degree : Nat) (seed : UInt64)
    (leading? : Option Int) : DensePoly Int × UInt64 :=
  let state := (Array.range (degree + 1)).foldl
    (fun state i =>
      let seed := nextSeed state.seed
      let raw := (Int.ofNat (seed.toNat % 21)) - 10
      let coefficient :=
        if i = degree then leading?.getD (if raw = 0 then 1 else raw)
        else raw
      { seed := seed, coeffs := state.coeffs.push coefficient })
    ({ seed := seed, coeffs := #[] } : PolyState)
  (ofCoeffs state.coeffs, state.seed)

/-- One exact-degree member of the committed fixture LCG family. -/
def densePoly (degree : Nat) (seed : UInt64) : DensePoly Int × UInt64 :=
  generatedPoly degree seed none

/-- Shared deterministic input family for resultant and discriminant. -/
def prepInput (n : Nat) : Input :=
  let (left, seed) := densePoly n initialSeed
  let (right, _) := densePoly n seed
  { left, right }

private def aggregateParams : Array Nat :=
  #[4, 6, 8, 10, 12, 16, 20, 24, 32]

-- Every aggregate rung reaches the terminal-constant resultant path; a hidden
-- common factor would otherwise make that rung under-measure Brown extraction.
#guard aggregateParams.all fun n =>
  let input := prepInput n
  resultant input.left input.right != 0

/-- Pseudo-division input with dividend degree `n` and divisor degree `n / 2`. -/
def prepPseudoInput (n : Nat) : Input :=
  let (left, seed) := generatedPoly n initialSeed (some 2)
  let (right, _) := generatedPoly (n / 2) seed (some 2)
  { left, right }

private def polyChecksum (p : DensePoly Int) : UInt64 :=
  hash p.toArray

private def chainChecksum (chain : Array (DensePoly Int)) : UInt64 :=
  chain.foldl
    (fun checksum polynomial => mixHash checksum (polyChecksum polynomial))
    (hash chain.size)

/-- Compute one public pseudo-division and force both outputs. -/
def runPseudoDiv (input : Input) : UInt64 :=
  let quotientRemainder := pseudoDivMod input.left input.right
  mixHash (polyChecksum quotientRemainder.1)
    (polyChecksum quotientRemainder.2)

/-- Compute and force the complete public subresultant chain. -/
def runChain (input : Input) : UInt64 :=
  chainChecksum (subresultantChain input.left input.right)

/-- Compute the public executable resultant. -/
def runResultant (input : Input) : Int :=
  resultant input.left input.right

/-- Compute the public executable discriminant. -/
def runDisc (input : Input) : Int :=
  disc input.left

/- A degree-`n` pseudo-division by degree `n/2` performs `O(n^2)` integer
coefficient operations. The fixture ladder crosses Lean's immediate-integer
boundary, so `wallCostModel` adds a logarithmic limb-growth proxy instead of
treating every arbitrary-precision coefficient operation as constant-cost.
The SPEC separately records the larger worst-case Hadamard bit-length bound. -/
def wallCostModel (n : Nat) : Nat :=
  n * n * (Nat.log2 (n + 1) + 1)

/- The pseudo-division fixture fixes both leading coefficients at two and its
ladder begins above the immediate-integer transition. There are `O(n^2)`
coefficient operations and linearly growing integer payloads across this
ladder, yielding the declared `O(n^3)` wallclock proxy. -/
setup_benchmark runPseudoDiv n => n * n * n
  with prep := prepPseudoInput
  where {
    paramFloor := 24
    paramCeiling := 128
    paramSchedule := .custom #[24, 32, 40, 48, 64, 80, 96, 128]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.3
  }

/- Brown's chain totals `O(n^2)` coefficient operations for equal degree
inputs. The stored-chain checksum forces every returned coefficient; the same
bounded-input bit-growth proxy used above therefore models its wallclock cost. -/
setup_benchmark runChain n => wallCostModel n
  with prep := prepInput
  where {
    paramFloor := 4
    paramCeiling := 32
    paramSchedule := .custom aggregateParams
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Resultant extraction is dominated by the same Brown chain. Its scalar
output is much larger than a machine integer at the upper rungs, so the cost-model
again includes the Hadamard bit-growth term rather than only counting loops. -/
setup_benchmark runResultant n => wallCostModel n
  with prep := prepInput
  where {
    paramFloor := 4
    paramCeiling := 32
    paramSchedule := .custom aggregateParams
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- `disc` forms the derivative in `O(n)` and runs one resultant between degrees
`n` and at most `n-1`. Brown and arbitrary-precision coefficient growth still
dominate, giving the same declared wallclock proxy. -/
setup_benchmark runDisc n => wallCostModel n
  with prep := prepInput
  where {
    paramFloor := 4
    paramCeiling := 32
    paramSchedule := .custom aggregateParams
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

end Hex.ResultantBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
