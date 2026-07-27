/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexResultant
import LeanBench

/-!
Benchmark registrations for `HexResultant`.

The two scientific families are the public operations required by the library
SPEC:

* `runResultant` computes the resultant of two deterministic dense integer
  polynomials of equal degree `n`;
* `runDisc` computes the discriminant of the left member of the same family.

Both inputs have bounded nonzero coefficients and nonzero leading coefficient.
There is no in-process external comparator: Mathlib's resultant is
noncomputable. Exact external cross-checking belongs to the JSONL conformance
driver, which uses FLINT and PARI.
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

/-- Deterministic bounded, nonzero coefficient keyed by degree, index, and salt. -/
def coeffValue (n i salt : Nat) : Int :=
  let magnitude := ((i + 3) * (salt + 17) + (i + 1) * (i + 7) * 13 + n * 29) % 19 + 1
  let value := Int.ofNat magnitude
  if (i + salt) % 2 = 0 then value else -value

/-- Dense integer polynomial of exact degree `n`. -/
def densePoly (n salt : Nat) : DensePoly Int :=
  ofCoeffs <| (Array.range (n + 1)).map fun i => coeffValue n i salt

/-- Shared deterministic input family for resultant and discriminant. -/
def prepInput (n : Nat) : Input :=
  { left := densePoly n 11
    right := densePoly n 37 }

/-- Compute the public executable resultant. -/
def runResultant (input : Input) : Int :=
  resultant input.left input.right

/-- Compute the public executable discriminant. -/
def runDisc (input : Input) : Int :=
  disc input.left

/- Brown's PRS performs at most `min(n,m)+1` pseudo-divisions and its nested
coefficient recurrences total `O(n*m)` coefficient operations. Here `n=m` is
the benchmark parameter, so the declared model is `O(n^2)`. -/
setup_benchmark runResultant n => n * n
  with prep := prepInput
  where {
    paramFloor := 4
    paramCeiling := 32
    paramSchedule := .custom #[4, 6, 8, 10, 12, 16, 20, 24, 32]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- `disc` forms the derivative in `O(n)` and then runs one resultant between
degrees `n` and at most `n-1`; the Brown recurrence therefore dominates at
`O(n^2)` coefficient operations on this family. -/
setup_benchmark runDisc n => n * n
  with prep := prepInput
  where {
    paramFloor := 4
    paramCeiling := 32
    paramSchedule := .custom #[4, 6, 8, 10, 12, 16, 20, 24, 32]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

end Hex.ResultantBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
