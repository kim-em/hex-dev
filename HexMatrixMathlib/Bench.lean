import HexMatrixMathlib.Determinant
import LeanBench

/-!
Benchmark registrations for the `HexMatrixMathlib` dense-matrix bridge.

This Phase 4 slice measures the representation conversion surfaces between the
executable `Hex.Matrix` representation and Mathlib's function-based `Matrix`
representation, row-operation bridge theorem surfaces, and the determinant
bridge theorem surface. Rank, span, and nullspace bridge benchmarks are left to
later Phase 4 slices.

Scientific registrations:

* `runMatrixEquivChecksum`: convert one generated dense square matrix to a
  Mathlib matrix and checksum its entries, `O(n^2)`.
* `runMatrixEquivSymmChecksum`: convert one generated Mathlib square matrix to a
  dense matrix and checksum its entries, `O(n^2)`.
* `runRoundTripChecksum`: perform both dense and Mathlib conversion round trips
  over generated square integer matrices, `O(n^2)`.
* `runHexRowSwapBridgeChecksum`: apply executable row swap, convert the result,
  and checksum all entries, `O(n^2)`.
* `runMathlibRowSwapChecksum`: apply the corresponding Mathlib row-swap matrix
  to the same fixture and checksum all entries, `O(n^2)`.
* `runHexRowScaleBridgeChecksum`: apply executable row scaling, convert the
  result, and checksum all entries, `O(n^2)`.
* `runMathlibRowScaleChecksum`: apply the corresponding Mathlib diagonal row
  scaling matrix to the same fixture and checksum all entries, `O(n^2)`.
* `runHexRowAddBridgeChecksum`: apply executable row addition, convert the
  result, and checksum all entries, `O(n^2)`.
* `runMathlibRowAddChecksum`: apply the corresponding Mathlib transvection to
  the same fixture and checksum all entries, `O(n^2)`.
* `runHexDetBridge`: convert a generated Mathlib matrix to `Hex.Matrix` and
  compute `Hex.Matrix.det`, using the Leibniz determinant model `O(n * n!)`.
* `runMathlibDetBridge`: convert the same generated dense matrix through
  `matrixEquiv` and compute `Matrix.det`, using the same textbook Leibniz
  determinant model.

Compare groups:

* `compare runHexDetBridge runMathlibDetBridge` checks the determinant bridge on
  the shared small-domain integer fixture schedule.
* `compare runHexRowSwapBridgeChecksum runMathlibRowSwapChecksum`,
  `compare runHexRowScaleBridgeChecksum runMathlibRowScaleChecksum`, and
  `compare runHexRowAddBridgeChecksum runMathlibRowAddChecksum` check the
  row-operation bridge surfaces on shared square integer fixture schedules.
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

/-- Per-parameter row-swap bridge fixture. -/
def prepRowSwapInput (n : Nat) : MatrixInput :=
  { n := n
    entries := flatMatrix n 257 }

/-- Per-parameter row-scale bridge fixture. -/
def prepRowScaleInput (n : Nat) : MatrixInput :=
  { n := n
    entries := flatMatrix n 293 }

/-- Per-parameter row-addition bridge fixture. -/
def prepRowAddInput (n : Nat) : MatrixInput :=
  { n := n
    entries := flatMatrix n 337 }

/-- Per-parameter determinant fixture shared by Hex and Mathlib determinant paths. -/
def prepDetInput (n : Nat) : DetInput :=
  { n := n
    entries := flatMatrix n 211 }

/-- First row index for a nonempty square matrix. -/
def firstRow (n : Nat) (h : 0 < n) : Fin n :=
  ⟨0, h⟩

/-- Last row index for a nonempty square matrix. -/
def lastRow (n : Nat) (h : 0 < n) : Fin n :=
  ⟨n - 1, Nat.sub_lt h (by decide)⟩

/-- Second row index for a matrix with at least two rows. -/
def secondRow (n : Nat) (h : 1 < n) : Fin n :=
  ⟨1, h⟩

/-- Fixed nontrivial scale factor used by row-operation bridge benchmarks. -/
def rowScaleCoeff : Int :=
  -3

/-- Fixed nontrivial transvection factor used by row-addition bridge benchmarks. -/
def rowAddCoeff : Int :=
  5

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

/-- Benchmark target: executable row swap followed by bridge conversion. -/
def runHexRowSwapBridgeChecksum (input : MatrixInput) : UInt64 :=
  let dense : Hex.Matrix Int input.n input.n := hexMatrixOfFlat input.n input.entries
  if h : 0 < input.n then
    let i := firstRow input.n h
    let j := lastRow input.n h
    checksumMathlib (matrixEquiv (Hex.Matrix.rowSwap dense i j))
  else
    checksumMathlib (matrixEquiv dense)

/-- Benchmark target: direct Mathlib-side row-swap construction. -/
def runMathlibRowSwapChecksum (input : MatrixInput) : UInt64 :=
  let dense : Hex.Matrix Int input.n input.n := hexMatrixOfFlat input.n input.entries
  let mathlib := matrixEquiv dense
  if h : 0 < input.n then
    let i := firstRow input.n h
    let j := lastRow input.n h
    checksumMathlib (Matrix.swap Int i j * mathlib)
  else
    checksumMathlib mathlib

/-- Benchmark target: executable row scaling followed by bridge conversion. -/
def runHexRowScaleBridgeChecksum (input : MatrixInput) : UInt64 :=
  let dense : Hex.Matrix Int input.n input.n := hexMatrixOfFlat input.n input.entries
  if h : 0 < input.n then
    let i := firstRow input.n h
    checksumMathlib (matrixEquiv (Hex.Matrix.rowScale dense i rowScaleCoeff))
  else
    checksumMathlib (matrixEquiv dense)

/-- Benchmark target: direct Mathlib-side row-scaling construction. -/
def runMathlibRowScaleChecksum (input : MatrixInput) : UInt64 :=
  let dense : Hex.Matrix Int input.n input.n := hexMatrixOfFlat input.n input.entries
  let mathlib := matrixEquiv dense
  if h : 0 < input.n then
    let i := firstRow input.n h
    checksumMathlib
      (Matrix.diagonal (Function.update (fun _ : Fin input.n => (1 : Int)) i rowScaleCoeff) *
        mathlib)
  else
    checksumMathlib mathlib

/-- Benchmark target: executable row addition followed by bridge conversion. -/
def runHexRowAddBridgeChecksum (input : MatrixInput) : UInt64 :=
  let dense : Hex.Matrix Int input.n input.n := hexMatrixOfFlat input.n input.entries
  if h : 1 < input.n then
    let src := firstRow input.n (Nat.zero_lt_of_lt h)
    let dst := secondRow input.n h
    checksumMathlib (matrixEquiv (Hex.Matrix.rowAdd dense src dst rowAddCoeff))
  else
    checksumMathlib (matrixEquiv dense)

/-- Benchmark target: direct Mathlib-side row-addition construction. -/
def runMathlibRowAddChecksum (input : MatrixInput) : UInt64 :=
  let dense : Hex.Matrix Int input.n input.n := hexMatrixOfFlat input.n input.entries
  let mathlib := matrixEquiv dense
  if h : 1 < input.n then
    let src := firstRow input.n (Nat.zero_lt_of_lt h)
    let dst := secondRow input.n h
    checksumMathlib (Matrix.transvection dst src rowAddCoeff * mathlib)
  else
    checksumMathlib mathlib

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

/- Cost model: executable row swap touches two dense rows, then the bridge view
and checksum force every entry of one generated `n x n` output matrix. -/
setup_benchmark runHexRowSwapBridgeChecksum n => n * n
  with prep := prepRowSwapInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 256, 384, 512]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: the direct Mathlib row-swap matrix is multiplied by the same
generated `n x n` matrix, and the checksum forces every output entry. -/
setup_benchmark runMathlibRowSwapChecksum n => n * n
  with prep := prepRowSwapInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 256, 384, 512]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: executable row scaling rewrites one dense row, then the bridge
view and checksum force every entry of one generated `n x n` output matrix. -/
setup_benchmark runHexRowScaleBridgeChecksum n => n * n
  with prep := prepRowScaleInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 256, 384, 512]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: the direct Mathlib diagonal row-scaling matrix is multiplied by
the same generated `n x n` matrix, and the checksum forces every output entry. -/
setup_benchmark runMathlibRowScaleChecksum n => n * n
  with prep := prepRowScaleInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 256, 384, 512]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: executable row addition rewrites one dense row, then the bridge
view and checksum force every entry of one generated `n x n` output matrix. -/
setup_benchmark runHexRowAddBridgeChecksum n => n * n
  with prep := prepRowAddInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 256, 384, 512]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: the direct Mathlib transvection is multiplied by the same
generated `n x n` matrix, and the checksum forces every output entry. -/
setup_benchmark runMathlibRowAddChecksum n => n * n
  with prep := prepRowAddInput
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
