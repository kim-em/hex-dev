import HexGramSchmidtMathlib.Conformance
import LeanBench

/-!
Benchmark registrations for the `HexGramSchmidtMathlib` Gram-Schmidt bridge.

This Phase 4 slice measures the computable bridge surfaces feeding the
Mathlib correspondence theorem and keeps small theorem-specialization checks in
the benchmark module so CI elaborates the public `gramSchmidt` bridge shape.

Scientific registrations:

* `runIntCastChecksum`: cast deterministic integer bases to rational matrices,
  `O(n^2)`.
* `runRatRowDotChecksum`: checksum all pairwise rational row dot products for
  deterministic rational rows, the executable counterpart of
  `rowToEuclidean_inner`, `O(n^3)` on `n x (2n + 1)` fixtures.
* `runBridgeElaborationChecksum`: fixed smoke target paired with theorem
  specializations for the rational and integer basis-to-Mathlib
  `gramSchmidt` correspondence.
-/

namespace Hex.GramSchmidtMathlibBench

/-- Flattened integer matrix input for bridge casts. -/
structure IntBridgeInput where
  rows : Nat
  cols : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

/-- Flattened rational matrix input for row-family bridge checks. -/
structure RatBridgeInput where
  rows : Nat
  cols : Nat
  entries : Array Rat
  deriving Repr, BEq, Hashable

/-- Deterministic mixing over machine words for compact benchmark observables. -/
def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

/-- Deterministic integer entry generator keyed by shape, coordinates, and salt. -/
def intEntryValue (rows cols row col salt : Nat) : Int :=
  let raw :=
    ((row + 1) * 1_103 +
      (col + 3) * 811 +
      (rows + 5) * 97 +
      (cols + 7) * 53 +
      salt) % 61
  Int.ofNat raw - 30

/-- Deterministic rational entry generator with bounded numerator and denominator. -/
def ratEntryValue (rows cols row col salt : Nat) : Rat :=
  let num := intEntryValue rows cols row col salt
  let den := ((row + 1) * 7 + (col + 2) * 5 + salt) % 9 + 1
  num / (den : Rat)

/-- Deterministic row-major integer matrix fixture. -/
def flatIntMatrix (rows cols salt : Nat) : Array Int :=
  if rows = 0 || cols = 0 then
    #[]
  else
    (Array.range (rows * cols)).map fun idx =>
      let row := idx / cols
      let col := idx % cols
      intEntryValue rows cols row col salt

/-- Deterministic row-major rational matrix fixture. -/
def flatRatMatrix (rows cols salt : Nat) : Array Rat :=
  if rows = 0 || cols = 0 then
    #[]
  else
    (Array.range (rows * cols)).map fun idx =>
      let row := idx / cols
      let col := idx % cols
      ratEntryValue rows cols row col salt

/-- Per-parameter integer fixture: an `n x (2n + 1)` deterministic basis. -/
def prepIntBridgeInput (n : Nat) : IntBridgeInput :=
  let cols := 2 * n + 1
  { rows := n
    cols := cols
    entries := flatIntMatrix n cols 47 }

/-- Per-parameter rational fixture: an `n x (2n + 1)` deterministic row family. -/
def prepRatBridgeInput (n : Nat) : RatBridgeInput :=
  let cols := 2 * n + 1
  { rows := n
    cols := cols
    entries := flatRatMatrix n cols 71 }

/-- Reconstruct a typed integer matrix from row-major entries. -/
def intMatrixOfFlat (input : IntBridgeInput) : Matrix Int input.rows input.cols :=
  Matrix.ofFn fun i j => input.entries.getD (i.val * input.cols + j.val) 0

/-- Reconstruct a typed rational matrix from row-major entries. -/
def ratMatrixOfFlat (input : RatBridgeInput) : Matrix Rat input.rows input.cols :=
  Matrix.ofFn fun i j => input.entries.getD (i.val * input.cols + j.val) 0

/-- Stable checksum for rational matrices. -/
def ratMatrixChecksum (M : Matrix Rat n m) : UInt64 :=
  (List.finRange n).foldl
    (fun acc i =>
      (List.finRange m).foldl
        (fun rowAcc j => mixWord rowAcc (hash M[i][j]))
        acc)
    0

/-- Stable checksum for all pairwise row dot products. -/
def rowDotChecksum (M : Matrix Rat n m) : UInt64 :=
  (List.finRange n).foldl
    (fun acc i =>
      (List.finRange n).foldl
        (fun rowAcc j => mixWord rowAcc (hash (Matrix.dot (M.row i) (M.row j))))
        acc)
    0

/-- Benchmark target: cast one integer basis through the Mathlib bridge surface. -/
def runIntCastChecksum (input : IntBridgeInput) : UInt64 :=
  ratMatrixChecksum (GramSchmidtMathlib.castIntMatrix (intMatrixOfFlat input))

/-- Benchmark target: executable rational row dot products used by
`rowToEuclidean_inner`. -/
def runRatRowDotChecksum (input : RatBridgeInput) : UInt64 :=
  rowDotChecksum (ratMatrixOfFlat input)

/-- Fixed target paired with the theorem-specialization checks below. -/
def runBridgeElaborationChecksum (_ : Unit) : UInt64 :=
  mixWord (hash "HexGramSchmidtMathlib.bridge") (hash "gramSchmidt")

private def theoremIntFixture : Matrix Int 3 5 :=
  Matrix.ofFn fun i j => intEntryValue 3 5 i.val j.val 113

private def theoremRatFixture : Matrix Rat 3 5 :=
  Matrix.ofFn fun i j => ratEntryValue 3 5 i.val j.val 127

private theorem intBasisBridgeSpecializes (i : Fin 3) :
    GramSchmidtMathlib.rowToEuclidean
        ((GramSchmidt.Int.basis theoremIntFixture).row i) =
      InnerProductSpace.gramSchmidt ℝ
        (GramSchmidtMathlib.intRowFamily theoremIntFixture) i := by
  exact GramSchmidtMathlib.int_basis_row_eq_gramSchmidt theoremIntFixture i

private theorem ratBasisBridgeSpecializes (i : Fin 3) :
    GramSchmidtMathlib.rowToEuclidean
        ((GramSchmidt.Rat.basis theoremRatFixture).row i) =
      InnerProductSpace.gramSchmidt ℝ
        (GramSchmidtMathlib.ratRowFamily theoremRatFixture) i := by
  exact GramSchmidtMathlib.rat_basis_row_eq_gramSchmidt theoremRatFixture i

/- Cost model: `castIntMatrix` maps every entry of the generated
`n x (2n + 1)` integer basis exactly once. -/
setup_benchmark runIntCastChecksum n => n * n
  with prep := prepIntBridgeInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 128, 256, 512]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: the fixture has `n` rational rows and `2n + 1` columns. The
target checks all row pairs and each dot product scans the ambient columns,
so the bridge-side row agreement checksum is cubic in `n`. -/
setup_benchmark runRatRowDotChecksum n => n * n * n
  with prep := prepRatBridgeInput
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 32, 64, 128]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_fixed_benchmark runBridgeElaborationChecksum where {
  repeats := 10
}

end Hex.GramSchmidtMathlibBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
