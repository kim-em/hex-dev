/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMatrix
import LeanBench

/-!
Benchmark registrations for `hex-matrix` (the dense base).

This Phase 4 slice measures dense square matrix multiplication on
deterministically generated integer inputs. Matrix construction is hoisted into
`prep` so the declared model tracks the timed algebraic operation rather than
fixture construction.

Scientific registration:

* `runSquareMulChecksum`: dense square multiplication, `O(n^3)`.

The dense base surfaces (multiplication, row operations on the structural
`Vector` / `Array` primitives) have no named external comparator (declared
absence with the `structural-layer` reason per
`SPEC/Libraries/hex-matrix.md §"External comparators"`). Determinant
benchmarks live in `hex-determinant` (Leibniz) and `hex-bareiss` (Bareiss,
with the FLINT comparator).
-/

namespace Hex.MatrixBench

/-- Flattened benchmark input for square matrix multiplication. The arrays
store `n * n` entries in row-major order. -/
structure MulInput where
  n : Nat
  lhs : Array Int
  rhs : Array Int
  deriving Repr, BEq, Hashable

/-- Deterministic pseudo-random-looking entry generator keyed by matrix
dimension, coordinates, and a salt distinguishing the two operands. -/
def entryValue (n row col salt : Nat) : Int :=
  let x : UInt64 :=
    (((n.toUInt64 + 1) * 0x9E3779B97F4A7C15) +
      ((row.toUInt64 + 1) * 0xBF58476D1CE4E5B9) +
      ((col.toUInt64 + 1) * 0x94D049BB133111EB) +
      salt.toUInt64)
  Int.ofNat (x.toNat % 65_521)

/-- Deterministic row-major matrix fixture of shape `n × n`. -/
def flatMatrix (n salt : Nat) : Array Int :=
  if n = 0 then
    #[]
  else
    (Array.range (n * n)).map fun idx =>
      let row := idx / n
      let col := idx % n
      entryValue n row col salt

/-- Per-parameter benchmark fixture: two deterministic square matrices. -/
def prepMulInput (n : Nat) : MulInput :=
  { n := n
    lhs := flatMatrix n 17
    rhs := flatMatrix n 43 }

/-- Reconstruct a typed dense square matrix from a row-major array. -/
def matrixOfFlat (n : Nat) (entries : Array Int) : Hex.Matrix Int n n :=
  Hex.Matrix.ofFn fun i j => entries.getD (i.val * n + j.val) 0

/-- Sum every entry so the benchmark returns a hashable observable of the
matrix product rather than the full matrix value. -/
def checksum (M : Hex.Matrix Int n n) : Int :=
  (List.finRange n).foldl
    (fun acc i =>
      (List.finRange n).foldl (fun rowAcc j => rowAcc + M[i][j]) acc)
    0

/-- Benchmark target: multiply the prepared matrices and checksum the
result. The timed work remains cubic in the matrix dimension. -/
def runSquareMulChecksum (input : MulInput) : Int :=
  let lhs : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.lhs
  let rhs : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.rhs
  checksum (lhs * rhs)

/-! `runSquareMulChecksum` cost model: textbook dense square multiplication is
`n` dot products per output row over `n` rows, each dot product `O(n)`, so the
declared model is the cubic `n * n * n`. -/
setup_benchmark runSquareMulChecksum n => n * n * n
  with prep := prepMulInput
  where {
    paramFloor := 160
    paramCeiling := 256
    paramSchedule := .custom #[160, 192, 224, 256]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
  }

end Hex.MatrixBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
