/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDeterminant
import LeanBench

/-!
Benchmark registrations for `hex-determinant`.

This Phase 4 slice measures the generic Leibniz-formula determinant on small
deterministically generated integer inputs. Matrix construction is hoisted into
`prep` so the declared model tracks the timed algebraic operation rather than
fixture construction.

Scientific registration:

* `runLeibnizDet`: generic Leibniz determinant, `O(n * n!)`, capped at small
  dimensions where the factorial permutation sum remains practical.

The Leibniz determinant has no external comparator: it is the reference
combinatorial definition, cross-checked against the row-pivoted Bareiss
determinant (`hex-bareiss`) for agreement rather than against an external tool
(declared absence with the `structural-layer` reason per
`SPEC/Libraries/hex-determinant.md §"External comparators"`).
-/

namespace Hex.DeterminantBench

/-- Flattened benchmark input for one square integer matrix. -/
structure DetInput where
  n : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

/-- Deterministic tridiagonal entries for determinant benchmarks. The shape
keeps intermediates small so the registration tests the permutation-sum scaling
rather than arbitrary-precision integer growth in random minors. -/
def smallEntryValue (_n row col salt : Nat) : Int :=
  if row = col then
    2 + (salt % 2)
  else if row + 1 = col then
    -1
  else if col + 1 = row then
    1
  else
    0

/-- Deterministic small-entry row-major matrix fixture of shape `n × n`. -/
def flatSmallMatrix (n salt : Nat) : Array Int :=
  if n = 0 then
    #[]
  else
    (Array.range (n * n)).map fun idx =>
      let row := idx / n
      let col := idx % n
      smallEntryValue n row col salt

/-- Per-parameter determinant fixture: one deterministic square matrix. -/
def prepDetInput (n : Nat) : DetInput :=
  { n := n
    entries := flatSmallMatrix n 71 }

/-- Reconstruct a typed dense square matrix from a row-major array. -/
def matrixOfFlat (n : Nat) (entries : Array Int) : Hex.Matrix Int n n :=
  Hex.Matrix.ofFn fun i j => entries.getD (i.val * n + j.val) 0

/-- Textbook operation-count model for the generic Leibniz determinant path:
the signed sum over all `n!` permutations, each an `n`-fold product. -/
def leibnizDetComplexity : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * leibnizDetComplexity n

/-- Benchmark target: compute the determinant using the generic Leibniz
definition. Capped at small dimensions where the factorial sum is practical. -/
def runLeibnizDet (input : DetInput) : Int :=
  let M : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.entries
  Hex.Matrix.det M

/-! `runLeibnizDet` cost model: the Leibniz determinant is the signed sum over
`n!` permutations of an `n`-fold diagonal product, so the operation count is
`n * n!`, i.e. `n * leibnizDetComplexity n`. -/
setup_benchmark runLeibnizDet n => n * leibnizDetComplexity n
  with prep := prepDetInput
  where {
    paramFloor := 2
    paramCeiling := 8
    paramSchedule := .custom #[2, 3, 4, 5, 6, 7, 8]
    maxSecondsPerCall := 1.5
    targetInnerNanos := 800000000
    verdictWarmupFraction := 0.5
  }

end Hex.DeterminantBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
