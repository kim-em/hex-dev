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

* `runSquareMulChecksum`: naive dense square multiplication, `O(n^3)`.
* `runSquareMulStrassenChecksum`: default-config Strassen-Winograd
  multiplication (`mulStrassen strassenDefault`), `Θ(n^{log₂ 7})`. On the
  power-of-two rungs both drivers share, the declared `Nat`-valued model
  `7 ^ Nat.log2 n` equals `n^{log₂ 7}` exactly (`7 ^ log₂ n = n^{log₂ 7}`).
* `runStrassenCut32` / `Cut64` / `Cut96` / `Cut128` / `Cut256`: the cutoff
  sweep — the same Strassen recursion at fixed cutoffs `τ ∈ {32, 64, 96, 128,
  256}`, a `compare` group over the shared rungs. The cutoff `τ` minimising time
  across the swept dimensions is the measured block-size crossover shipped as
  `strassenDefault.cutoff = 96` (SPEC/hex-matrix.md §Benchmarks). This is a local
  / scheduled-hardware sweep, not a merge-gating CI activity.

The two scaling series (`runSquareMulChecksum`, `runSquareMulStrassenChecksum`)
back `reports/figures/hex-matrix-mul-scaling.svg` via
`scripts/plots/hex-matrix-mul-scaling.py`.

The dense base surfaces (multiplication, row operations on the structural
`Vector` / `Array` primitives) have no named external comparator (declared
absence with the `structural-layer` reason per
`SPEC/Libraries/hex-matrix.md §"External comparators"`). The Strassen driver
declares the same structural-layer absence: its baseline is the internal naive
`mul`, not an external tool. Determinant benchmarks live in `hex-determinant`
(Leibniz) and `hex-bareiss` (Bareiss, with the FLINT comparator).
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
      (List.finRange n).foldl (fun rowAcc j => rowAcc + M[(i, j)]) acc)
    0

/-- Benchmark target: multiply the prepared matrices with the naive `mul` and
checksum the result. The timed work remains cubic in the matrix dimension. -/
def runSquareMulChecksum (input : MulInput) : Int :=
  let lhs : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.lhs
  let rhs : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.rhs
  checksum (lhs * rhs)

/-- A Strassen configuration over `Int` at a chosen `cutoff`, with the naive
`mulImpl` base kernel (exactly `strassenDefault` but with `cutoff` overridden).
Used by the cutoff sweep. -/
def strassenAt (cutoff : Nat) : Hex.Matrix.StrassenConfig Int where
  cutoff := cutoff
  baseMul := Hex.Matrix.mulImpl

/-- Multiply the prepared matrices with `mulStrassen` at a given `cutoff` and
checksum the result. -/
def runStrassenAt (cutoff : Nat) (input : MulInput) : Int :=
  let lhs : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.lhs
  let rhs : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.rhs
  checksum (Hex.Matrix.mulStrassen (strassenAt cutoff) lhs rhs)

/-- Benchmark target: default-config Strassen-Winograd multiplication. This is
the shipped `strassenDefault` (its `cutoff` is the measured crossover), so this
target tracks the constant automatically. -/
def runSquareMulStrassenChecksum (input : MulInput) : Int :=
  let lhs : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.lhs
  let rhs : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.rhs
  checksum (Hex.Matrix.mulStrassen Hex.Matrix.strassenDefault lhs rhs)

/-- Cutoff-sweep targets: the Strassen recursion at fixed cutoffs bracketing the
shipped `strassenDefault.cutoff = 96`. On power-of-two rungs the recursion tree
depends only on the leaf-block class, so these five span the distinguishable
classes: `Cut32` (leaf 16), `Cut64` (leaf 32), `Cut96`/`Cut128` (leaf 64, the
in-context optimum, identical on powers of two), and `Cut256` (leaf 128). -/
def runStrassenCut32 (input : MulInput) : Int := runStrassenAt 32 input
def runStrassenCut64 (input : MulInput) : Int := runStrassenAt 64 input
def runStrassenCut96 (input : MulInput) : Int := runStrassenAt 96 input
def runStrassenCut128 (input : MulInput) : Int := runStrassenAt 128 input
def runStrassenCut256 (input : MulInput) : Int := runStrassenAt 256 input

/-! `runSquareMulChecksum` cost model: textbook dense square multiplication is
`n` dot products per output row over `n` rows, each dot product `O(n)`, so the
declared model is the cubic `n * n * n`. The power-of-two rungs are shared with
the Strassen series so the two scaling curves overlay cleanly. -/
setup_benchmark runSquareMulChecksum n => n * n * n
  with prep := prepMulInput
  where {
    paramFloor := 64
    paramCeiling := 1024
    paramSchedule := .custom #[64, 128, 256, 512, 1024]
    maxSecondsPerCall := 90.0
    targetInnerNanos := 500000000
  }

/-! `runSquareMulStrassenChecksum` cost model: Strassen-Winograd does **seven**
recursive block products per 2×2 level down to the cutoff, one fewer than the
eight of the naive block product, giving `Θ(n^{log₂ 7})` coefficient
multiplications. Since `n^{log₂ 7} = 7^{log₂ n}`, the exact `Nat`-valued model
on power-of-two rungs is `7 ^ Nat.log2 n`. The declared model tracks the
sub-cubic exponent so regression tracking uses `log₂ 7`, not `3`. -/
setup_benchmark runSquareMulStrassenChecksum n => 7 ^ Nat.log2 n
  with prep := prepMulInput
  where {
    paramFloor := 64
    paramCeiling := 1024
    paramSchedule := .custom #[64, 128, 256, 512, 1024]
    maxSecondsPerCall := 90.0
    targetInnerNanos := 500000000
  }

/-! Cutoff-sweep registrations. Same Strassen model as the default target; they
differ only in the fixed cutoff. The `compare` group over these targets locates
the block-size crossover. -/
setup_benchmark runStrassenCut32 n => 7 ^ Nat.log2 n
  with prep := prepMulInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 128, 256, 512]
    maxSecondsPerCall := 40.0
    targetInnerNanos := 500000000
  }
setup_benchmark runStrassenCut64 n => 7 ^ Nat.log2 n
  with prep := prepMulInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 128, 256, 512]
    maxSecondsPerCall := 40.0
    targetInnerNanos := 500000000
  }
setup_benchmark runStrassenCut128 n => 7 ^ Nat.log2 n
  with prep := prepMulInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 128, 256, 512]
    maxSecondsPerCall := 40.0
    targetInnerNanos := 500000000
  }
setup_benchmark runStrassenCut96 n => 7 ^ Nat.log2 n
  with prep := prepMulInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 128, 256, 512]
    maxSecondsPerCall := 40.0
    targetInnerNanos := 500000000
  }
setup_benchmark runStrassenCut256 n => 7 ^ Nat.log2 n
  with prep := prepMulInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 128, 256, 512]
    maxSecondsPerCall := 40.0
    targetInnerNanos := 500000000
  }

end Hex.MatrixBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
