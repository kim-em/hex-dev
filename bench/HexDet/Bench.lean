/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDet
import LeanBench

/-!
Benchmark registrations for `hex-det`.

The measured question this library owns is which arm dispatch should select, so
the registrations are internal adjacent-arm comparisons: fraction-free Bareiss
against Berkowitz on identical inputs, and dispatch against the arm it selects.
External comparators are informational and belong to the headline report, not to
the selection decision.

Scientific registrations, one per Phase-4 input family:

* `runDetInt`: dispatch over `Int`, `O(n^3)`.
* `runDetRat`: dispatch over `Rat`, `O(n^3)` ring operations.
* `runDetPoly`: dispatch over `Hex.DensePoly Int`, `O(n^4)`: `O(n^3)` polynomial
  operations on entries whose degree grows linearly in the dimension.
* `runDetMv`: dispatch over `Hex.MvPoly 2 Int`, `O(n^4)` for the same reason.
* `runBerkowitzInt`: the Berkowitz arm over `Int`, `O(n^4)`.

Fixed rungs pair each arm with the other on the same prepared input, so a
comparison run alternates two adjacent arms rather than two fixture families.

`verify` also runs the route-agreement canary, which checks that dispatch
reports the small arm exactly at `n ≤ 2` and its recipe's own arm above, and
that each arm returns the value its recipe promises on bounded fixtures.

This target is Mathlib-free, as every `hex-det` bench target must be.
-/

namespace Hex.DetBench

open Hex Hex.Det

/-- Flattened benchmark input for one square matrix. -/
structure DetInput where
  /-- Dimension. -/
  n : Nat
  /-- Row-major entries. -/
  entries : Array Int
  deriving Repr, BEq, Hashable

/-- Deterministic tridiagonal entries. The shape keeps fraction-free
intermediates small, so a registration measures the elimination loop rather than
arbitrary-precision growth in random minors. -/
def smallEntryValue (row col salt : Nat) : Int :=
  if row = col then 2 + (salt % 2)
  else if row + 1 = col then -1
  else if col + 1 = row then 1
  else 0

/-- Deterministic row-major fixture of shape `n × n`. -/
def flatSmallMatrix (n salt : Nat) : Array Int :=
  (Array.range (n * n)).map fun idx => smallEntryValue (idx / n) (idx % n) salt

/-- Per-parameter fixture: one deterministic square matrix. -/
def prepDetInput (n : Nat) : DetInput :=
  { n := n, entries := flatSmallMatrix n 71 }

/-- Reconstruct a typed dense square matrix from a row-major array. -/
def matrixOfFlat (n : Nat) (entries : Array Int) : Matrix Int n n :=
  Matrix.ofFn fun i j => entries.getD (i.val * n + j.val) 0

/-- Reconstruct the same fixture over the rationals. -/
def ratMatrixOfFlat (n : Nat) (entries : Array Int) : Matrix Rat n n :=
  Matrix.ofFn fun i j => ((entries.getD (i.val * n + j.val) 0 : Int) : Rat) / 3

/-- Reconstruct the same fixture with linear polynomial entries, so every
division the Bareiss recurrence performs is by a nonconstant pivot. -/
def polyMatrixOfFlat (n : Nat) (entries : Array Int) : Matrix (DensePoly Int) n n :=
  Matrix.ofFn fun i j =>
    let a := entries.getD (i.val * n + j.val) 0
    DensePoly.ofList [a, a + 1]

/-- The same fixture over two-variable polynomials. -/
def mvMatrixOfFlat (n : Nat) (entries : Array Int) :
    Matrix (MvPoly 2 Int Mono.grevlex) n n :=
  Matrix.ofFn fun i j =>
    let a := entries.getD (i.val * n + j.val) 0
    MvPoly.ofTerms [(Vector.ofFn fun _ => 1, a), (Vector.ofFn fun _ => 0, a + 1)]

/-- Benchmark target: the determinant dispatch returns over `Int`. -/
def runDetInt (input : DetInput) : Int :=
  Hex.Det.det (matrixOfFlat input.n input.entries)

/-- The Bareiss arm over `Int`, called directly. -/
def runBareissInt (input : DetInput) : Int :=
  Matrix.bareiss (matrixOfFlat input.n input.entries)

/-- The Berkowitz arm over `Int`, called directly. -/
def runBerkowitzInt (input : DetInput) : Int :=
  berkowitzDet (matrixOfFlat input.n input.entries)

/-- Benchmark target: the determinant dispatch returns over `Rat`. -/
def runDetRat (input : DetInput) : Rat :=
  Hex.Det.det (ratMatrixOfFlat input.n input.entries)

/-- Benchmark target: dispatch over dense integer polynomials, reported by its
coefficient count so the registration records a bounded scalar. Reading the size
forces the whole determinant. -/
def runDetPoly (input : DetInput) : Nat :=
  (Hex.Det.det (polyMatrixOfFlat input.n input.entries)).size

/-- The Bareiss arm over dense integer polynomials, called directly. -/
def runBareissPoly (input : DetInput) : DensePoly Int :=
  Matrix.bareissWith Hex.exactDiv (polyMatrixOfFlat input.n input.entries)

/-- The Berkowitz arm over dense integer polynomials, called directly. -/
def runBerkowitzPoly (input : DetInput) : DensePoly Int :=
  berkowitzDet (polyMatrixOfFlat input.n input.entries)

/-- Benchmark target: dispatch over two-variable polynomials, reported by its
term count for the same reason. -/
def runDetMv (input : DetInput) : Nat :=
  (Hex.Det.det (mvMatrixOfFlat input.n input.entries)).termCount

/-! Per-rung wrappers for the paired fixed registrations. Each captures its
prepared input outside the timed closure, so both arms of a comparison see the
same matrix and neither is charged for building it. -/

def runDetIntAt (n : Nat) : Unit → IO Int :=
  let input := prepDetInput n
  fun _ => return runDetInt input
def runBareissIntAt (n : Nat) : Unit → IO Int :=
  let input := prepDetInput n
  fun _ => return runBareissInt input
def runBerkowitzIntAt (n : Nat) : Unit → IO Int :=
  let input := prepDetInput n
  fun _ => return runBerkowitzInt input
def runBareissPolyAt (n : Nat) : Unit → IO Nat :=
  let input := prepDetInput n
  fun _ => return (runBareissPoly input).size
def runBerkowitzPolyAt (n : Nat) : Unit → IO Nat :=
  let input := prepDetInput n
  fun _ => return (runBerkowitzPoly input).size

def runDetInt6 : Unit → IO Int := runDetIntAt 6
def runBareissInt6 : Unit → IO Int := runBareissIntAt 6
def runBerkowitzInt6 : Unit → IO Int := runBerkowitzIntAt 6
def runDetInt10 : Unit → IO Int := runDetIntAt 10
def runBareissInt10 : Unit → IO Int := runBareissIntAt 10
def runBerkowitzInt10 : Unit → IO Int := runBerkowitzIntAt 10
def runDetInt16 : Unit → IO Int := runDetIntAt 16
def runBareissInt16 : Unit → IO Int := runBareissIntAt 16
def runBerkowitzInt16 : Unit → IO Int := runBerkowitzIntAt 16
def runDetInt24 : Unit → IO Int := runDetIntAt 24
def runBareissInt24 : Unit → IO Int := runBareissIntAt 24
def runBerkowitzInt24 : Unit → IO Int := runBerkowitzIntAt 24
def runBareissPoly4 : Unit → IO Nat := runBareissPolyAt 4
def runBerkowitzPoly4 : Unit → IO Nat := runBerkowitzPolyAt 4
def runBareissPoly6 : Unit → IO Nat := runBareissPolyAt 6
def runBerkowitzPoly6 : Unit → IO Nat := runBerkowitzPolyAt 6
def runBareissPoly8 : Unit → IO Nat := runBareissPolyAt 8
def runBerkowitzPoly8 : Unit → IO Nat := runBerkowitzPolyAt 8

/-- Route-agreement and bounded-output canary.

Dispatch must report the small arm exactly at `n ≤ 2` and its recipe's own arm
above, the value it returns must be the one its selected arm computes, and the
explicitly forced recipes must agree with it. Returns the number of checks
performed so a run records a stable, bounded output. -/
def runRouteAgreement (_ : Unit) : IO Nat := do
  let mut checks := 0
  for n in [0, 1, 2] do
    let input := prepDetInput n
    let matrix := matrixOfFlat n input.entries
    unless (DetOps.run matrix).route.attempts == [Arm.small] do
      throw <| IO.userError s!"dispatch did not report the small arm at n = {n}"
    unless Hex.Det.det matrix == Matrix.det matrix do
      throw <| IO.userError s!"small arm disagreed with the reference at n = {n}"
    checks := checks + 2
  for n in [3, 5, 8] do
    let input := prepDetInput n
    let matrix := matrixOfFlat n input.entries
    unless (DetOps.run matrix).route.attempts == [Arm.bareiss] do
      throw <| IO.userError s!"integer dispatch did not report Bareiss at n = {n}"
    unless Hex.Det.det matrix == runBareissInt input do
      throw <| IO.userError s!"dispatch disagreed with its Bareiss arm at n = {n}"
    unless Hex.Det.det matrix == runBerkowitzInt input do
      throw <| IO.userError s!"the two arms disagreed at n = {n}"
    unless (runWith (Policy.berkowitz inferInstance) matrix).value == Hex.Det.det matrix do
      throw <| IO.userError s!"the forced Berkowitz recipe disagreed at n = {n}"
    checks := checks + 4
    let polyMatrix := polyMatrixOfFlat n input.entries
    unless (DetOps.run polyMatrix).route.attempts == [Arm.bareiss] do
      throw <| IO.userError s!"polynomial dispatch did not report Bareiss at n = {n}"
    unless Hex.Det.det polyMatrix == runBerkowitzPoly input do
      throw <| IO.userError s!"the two polynomial arms disagreed at n = {n}"
    checks := checks + 2
  return checks

/-! `runDetInt` cost model: dispatch runs fraction-free Bareiss above the small
sizes, which performs `O(n^3)` ring operations across its `n` elimination
stages. -/
setup_benchmark runDetInt n => n * n * n
  with prep := prepDetInput
  where {
    paramFloor := 8
    paramCeiling := 16
    paramSchedule := .custom #[8, 12, 16]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 2000000000
  }

/-! `runDetRat` cost model: the same cubic elimination, with rational
coefficient arithmetic in place of integer arithmetic. -/
setup_benchmark runDetRat n => n * n * n
  with prep := prepDetInput
  where {
    paramFloor := 6
    paramCeiling := 12
    paramSchedule := .custom #[6, 9, 12]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 2000000000
  }

/-! `runDetPoly` cost model: the elimination performs `O(n^3)` polynomial
operations, but the entries do not stay bounded. Fraction-free elimination on
linear entries reaches degree `O(n)`, and one dense product of degree-`O(n)`
operands costs `O(n)` coefficient operations, so the declared model is `n^4`. -/
setup_benchmark runDetPoly n => n * n * n * n
  with prep := prepDetInput
  where {
    paramFloor := 4
    paramCeiling := 8
    paramSchedule := .custom #[4, 6, 8]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 2000000000
  }

/-! `runDetMv` cost model: the same `O(n^3)` polynomial operations, with support
growing through the elimination as in the dense-polynomial case, so the declared
model is again `n^4`. -/
setup_benchmark runDetMv n => n * n * n * n
  with prep := prepDetInput
  where {
    paramFloor := 3
    paramCeiling := 6
    paramSchedule := .custom #[3, 4, 6]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 2000000000
  }

/-! `runBerkowitzInt` cost model: the Samuelson--Berkowitz recurrence performs
`O(n^4)` ring operations, one Toeplitz product per stage. -/
setup_benchmark runBerkowitzInt n => n * n * n * n
  with prep := prepDetInput
  where {
    paramFloor := 6
    paramCeiling := 12
    paramSchedule := .custom #[6, 9, 12]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 2000000000
  }

/-! # Adjacent-arm fixed rungs

Each rung registers the two arms on the identical prepared input. A comparison
run alternates them, so the recorded ratio is the arm difference at that
dimension and nothing else. The dispatch rungs measure interpretation overhead
against the arm dispatch selects. -/

def armConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 6.0, minTotalSeconds := 0.2,
    warmupFirstIter := true }

setup_fixed_benchmark runRouteAgreement where armConfig

setup_fixed_benchmark runDetInt6 where armConfig
setup_fixed_benchmark runBareissInt6 where armConfig
setup_fixed_benchmark runBerkowitzInt6 where armConfig
setup_fixed_benchmark runDetInt10 where armConfig
setup_fixed_benchmark runBareissInt10 where armConfig
setup_fixed_benchmark runBerkowitzInt10 where armConfig
setup_fixed_benchmark runDetInt16 where armConfig
setup_fixed_benchmark runBareissInt16 where armConfig
setup_fixed_benchmark runBerkowitzInt16 where armConfig
setup_fixed_benchmark runDetInt24 where armConfig
setup_fixed_benchmark runBareissInt24 where armConfig
setup_fixed_benchmark runBerkowitzInt24 where armConfig
setup_fixed_benchmark runBareissPoly4 where armConfig
setup_fixed_benchmark runBerkowitzPoly4 where armConfig
setup_fixed_benchmark runBareissPoly6 where armConfig
setup_fixed_benchmark runBerkowitzPoly6 where armConfig
setup_fixed_benchmark runBareissPoly8 where armConfig
setup_fixed_benchmark runBerkowitzPoly8 where armConfig

end Hex.DetBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
