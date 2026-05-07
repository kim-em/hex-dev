import HexMatrixMathlib.Determinant
import LeanBench

/-!
Benchmark registrations for the `HexMatrixMathlib` dense-matrix bridge.

This Phase 4 slice measures the representation conversion surfaces between the
executable `Hex.Matrix` representation and Mathlib's function-based `Matrix`
representation, plus the determinant bridge theorem surface. Row-operation,
rank, span, and nullspace bridge benchmarks are left to later Phase 4 slices.

Scientific registrations:

* `runMatrixEquivChecksum`: convert one generated dense square matrix to a
  Mathlib matrix and checksum its entries, `O(n^2)`.
* `runMatrixEquivSymmChecksum`: convert one generated Mathlib square matrix to a
  dense matrix and checksum its entries, `O(n^2)`.
* `runRoundTripChecksum`: perform both dense and Mathlib conversion round trips
  over generated square integer matrices, `O(n^2)`.
* `runHexDetBridge`: convert a generated Mathlib matrix to `Hex.Matrix` and
  compute `Hex.Matrix.det`, using the Leibniz determinant model `O(n * n!)`.
* `runMathlibDetBridge`: convert the same generated dense matrix through
  `matrixEquiv` and compute `Matrix.det`, using the same textbook Leibniz
  determinant model.

Compare groups:

* `compare runHexDetBridge runMathlibDetBridge` checks the determinant bridge on
  the shared small-domain integer fixture schedule.
-/

namespace HexMatrixMathlib.MatrixBench

/-- Flattened benchmark input for one square integer matrix. -/
structure MatrixInput where
  n : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

/-- Prepared paired dense and Mathlib bridge inputs for round-trip checksums. -/
structure RoundTripInput where
  n : Nat
  denseEntries : Array Int
  mathlibEntries : Array Int
  deriving Repr, BEq, Hashable

/-- Flattened benchmark input for determinant bridge checks. -/
structure DetInput where
  n : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

/-- Deterministic mixing over machine words for compact benchmark observables. -/
def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

/-- Deterministic matrix entry generator keyed by dimension, coordinates, and salt. -/
def entryValue (n row col salt : Nat) : Int :=
  let raw :=
    ((row + 1) * (salt + 17) +
      (col + 3) * (col + 5) * 13 +
      (row + col + 7) * n * 29) % 4093
  Int.ofNat raw - 2046

/-- Deterministic row-major square matrix fixture of shape `n x n`. -/
def flatMatrix (n salt : Nat) : Array Int :=
  if n = 0 then
    #[]
  else
    (Array.range (n * n)).map fun idx =>
      let row := idx / n
      let col := idx % n
      entryValue n row col salt

/-- Reconstruct a typed dense square matrix from a row-major array. -/
def hexMatrixOfFlat (n : Nat) (entries : Array Int) : Hex.Matrix Int n n :=
  Hex.Matrix.ofFn fun i j => entries.getD (i.val * n + j.val) 0

/-- Reconstruct a typed Mathlib square matrix from a row-major array. -/
def mathlibMatrixOfFlat (n : Nat) (entries : Array Int) : Matrix (Fin n) (Fin n) Int :=
  fun i j => entries.getD (i.val * n + j.val) 0

/-- Stable checksum for a dense matrix's entries. -/
def checksumHex (M : Hex.Matrix Int n n) : UInt64 :=
  (List.finRange n).foldl
    (fun acc i =>
      (List.finRange n).foldl
        (fun rowAcc j => mixWord rowAcc (hash M[i][j]))
        acc)
    0

/-- Stable checksum for a Mathlib matrix's entries. -/
def checksumMathlib (M : Matrix (Fin n) (Fin n) Int) : UInt64 :=
  (List.finRange n).foldl
    (fun acc i =>
      (List.finRange n).foldl
        (fun rowAcc j => mixWord rowAcc (hash (M i j)))
        acc)
    0

/-- Per-parameter dense fixture for conversion to Mathlib. -/
def prepDenseInput (n : Nat) : MatrixInput :=
  { n := n
    entries := flatMatrix n 53 }

/-- Per-parameter Mathlib fixture for conversion back to dense form. -/
def prepMathlibInput (n : Nat) : MatrixInput :=
  { n := n
    entries := flatMatrix n 89 }

/-- Per-parameter paired fixture for both conversion round trips. -/
def prepRoundTripInput (n : Nat) : RoundTripInput :=
  { n := n
    denseEntries := flatMatrix n 131
    mathlibEntries := flatMatrix n 173 }

/-- Per-parameter determinant fixture shared by Hex and Mathlib determinant paths. -/
def prepDetInput (n : Nat) : DetInput :=
  { n := n
    entries := flatMatrix n 211 }

/-- Benchmark target: convert one dense matrix and checksum Mathlib entries. -/
def runMatrixEquivChecksum (input : MatrixInput) : UInt64 :=
  let dense : Hex.Matrix Int input.n input.n := hexMatrixOfFlat input.n input.entries
  checksumMathlib (matrixEquiv dense)

/-- Benchmark target: convert one Mathlib matrix and checksum dense entries. -/
def runMatrixEquivSymmChecksum (input : MatrixInput) : UInt64 :=
  let mathlib : Matrix (Fin input.n) (Fin input.n) Int :=
    mathlibMatrixOfFlat input.n input.entries
  checksumHex (matrixEquiv.symm mathlib)

/-- Benchmark target: checksum both dense and Mathlib conversion round trips. -/
def runRoundTripChecksum (input : RoundTripInput) : UInt64 :=
  let dense : Hex.Matrix Int input.n input.n :=
    hexMatrixOfFlat input.n input.denseEntries
  let mathlib : Matrix (Fin input.n) (Fin input.n) Int :=
    mathlibMatrixOfFlat input.n input.mathlibEntries
  let denseRoundTrip := matrixEquiv.symm (matrixEquiv dense)
  let mathlibRoundTrip := matrixEquiv (matrixEquiv.symm mathlib)
  mixWord (checksumHex denseRoundTrip) (checksumMathlib mathlibRoundTrip)

/-- Benchmark target: convert from Mathlib representation and compute Hex's determinant. -/
def runHexDetBridge (input : DetInput) : Int :=
  let mathlib : Matrix (Fin input.n) (Fin input.n) Int :=
    mathlibMatrixOfFlat input.n input.entries
  let dense : Hex.Matrix Int input.n input.n := matrixEquiv.symm mathlib
  Hex.Matrix.det dense

/-- Benchmark target: convert from dense representation and compute Mathlib's determinant. -/
def runMathlibDetBridge (input : DetInput) : Int :=
  let dense : Hex.Matrix Int input.n input.n := hexMatrixOfFlat input.n input.entries
  Matrix.det (matrixEquiv dense)

/-- Textbook Leibniz determinant operation-count model, `n!`. -/
def determinantFactorialComplexity : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * determinantFactorialComplexity n

/-- Textbook determinant bridge model for the Leibniz sum, `O(n * n!)`. -/
def determinantBridgeComplexity (n : Nat) : Nat :=
  n * determinantFactorialComplexity n

/- Cost model: `matrixEquiv` exposes each dense matrix entry through a function
view. The checksum forces every entry of the generated `n x n` matrix once. -/
setup_benchmark runMatrixEquivChecksum n => n * n
  with prep := prepDenseInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 256, 384, 512]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: `matrixEquiv.symm` rebuilds a dense `Vector`-backed matrix by
enumerating the generated `n x n` Mathlib matrix entries once. -/
setup_benchmark runMatrixEquivSymmChecksum n => n * n
  with prep := prepMathlibInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 256, 384, 512]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: the round-trip target performs one conversion in each direction
for dense-origin and Mathlib-origin inputs. Each pass visits `n^2` entries. -/
setup_benchmark runRoundTripChecksum n => n * n
  with prep := prepRoundTripInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 256, 384, 512]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: `Hex.Matrix.det` uses the Leibniz formula. The bridge conversion
is quadratic, dominated on the shared comparison domain by the `n!` terms, each
touching `n` entries. -/
setup_benchmark runHexDetBridge n => determinantBridgeComplexity n
  with prep := prepDetInput
  where {
    paramFloor := 3
    paramCeiling := 7
    paramSchedule := .custom #[3, 4, 5, 6, 7]
    maxSecondsPerCall := 1.5
    targetInnerNanos := 800000000
    verdictWarmupFraction := 0.5
    signalFloorMultiplier := 1.0
  }

/- Cost model: Mathlib's determinant is exercised through the same Leibniz
determinant model on the same fixture schedule; `matrixEquiv` conversion is
quadratic and does not dominate the determinant work. -/
setup_benchmark runMathlibDetBridge n => determinantBridgeComplexity n
  with prep := prepDetInput
  where {
    paramFloor := 3
    paramCeiling := 7
    paramSchedule := .custom #[3, 4, 5, 6, 7]
    maxSecondsPerCall := 1.5
    targetInnerNanos := 800000000
    verdictWarmupFraction := 0.5
    signalFloorMultiplier := 1.0
  }

end HexMatrixMathlib.MatrixBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
