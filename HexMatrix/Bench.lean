import HexMatrix
import Hex.BenchOracle.Flint
import Lean.Data.Json
import LeanBench

/-!
Benchmark registrations for `hex-matrix`.

This Phase 4 slice measures dense square matrix multiplication and determinant
computation on deterministically generated integer inputs. Matrix construction
is hoisted into `prep` for every parametric family, so each declared model
tracks the timed algebraic operation rather than fixture construction.

Scientific registrations:

* `runSquareMulChecksum`: dense square multiplication, `O(n^3)`.
* `runBareissDet`: row-pivoted Bareiss determinant over `Int`, `O(n^3)`.

Small-domain cross-check registrations:

* `runLeibnizDet`: generic Leibniz determinant, `O(n * n!)`, capped at small
  dimensions so `compare runBareissDet runLeibnizDet` exercises the shared
  determinant API where both implementations are practical.

Informational external comparator (FLINT `fmpz_mat_det` via the shared
persistent-subprocess python-flint driver, per
`SPEC/Libraries/hex-matrix.md §"External comparators"` and
`SPEC/benchmarking.md §"External comparators" §"Process call"`):

* `runFlintBareissDet*` ↔ `runBareissDet*` (`fmpz_mat.det`).

FLINT's determinant uses multimodular reduction + CRT, structurally
different from Hex's fraction-free Bareiss elimination; the ratio is
recorded for orientation but does not block Phase 4. Other Phase-4
matrix surfaces (`runSquareMulChecksum`, row operations) have no
named external comparator (declared absence with the
`structural-layer` reason per
`SPEC/Libraries/hex-matrix.md §"External comparators"`).
-/

namespace Hex.MatrixBench

/-- Flattened benchmark input for square matrix multiplication. The arrays
store `n * n` entries in row-major order. -/
structure MulInput where
  n : Nat
  lhs : Array Int
  rhs : Array Int
  deriving Repr, BEq, Hashable

/-- Flattened benchmark input for one square integer matrix. -/
structure DetInput where
  n : Nat
  entries : Array Int
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

/-- Deterministic tridiagonal entries for determinant benchmarks. The shape
keeps Bareiss intermediates small so the registration tests elimination-loop
scaling rather than arbitrary-precision integer growth in random minors. -/
def smallEntryValue (_n row col salt : Nat) : Int :=
  if row = col then
    2 + (salt % 2)
  else if row + 1 = col then
    -1
  else if col + 1 = row then
    1
  else
    0

/-- Deterministic row-major matrix fixture of shape `n × n`. -/
def flatMatrix (n salt : Nat) : Array Int :=
  if n = 0 then
    #[]
  else
    (Array.range (n * n)).map fun idx =>
      let row := idx / n
      let col := idx % n
      entryValue n row col salt

/-- Deterministic small-entry row-major matrix fixture of shape `n × n`. -/
def flatSmallMatrix (n salt : Nat) : Array Int :=
  if n = 0 then
    #[]
  else
    (Array.range (n * n)).map fun idx =>
      let row := idx / n
      let col := idx % n
      smallEntryValue n row col salt

/-- Per-parameter benchmark fixture: two deterministic square matrices. -/
def prepMulInput (n : Nat) : MulInput :=
  { n := n
    lhs := flatMatrix n 17
    rhs := flatMatrix n 43 }

/-- Per-parameter determinant fixture: one deterministic square matrix. -/
def prepDetInput (n : Nat) : DetInput :=
  { n := n
    entries := flatSmallMatrix n 71 }

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

/-- Benchmark target: compute the determinant using row-pivoted Bareiss
elimination. Fixture construction is supplied by `prepDetInput`. -/
def runBareissDet (input : DetInput) : Int :=
  let M : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.entries
  Hex.Matrix.bareiss M

/-- Benchmark target: compute the same determinant using the generic Leibniz
definition. This is intended only for small-domain conformance comparison. -/
def runLeibnizDet (input : DetInput) : Int :=
  let M : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.entries
  Hex.Matrix.det M

/-- Textbook operation-count model for the generic Leibniz determinant path. -/
def leibnizDetComplexity : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * leibnizDetComplexity n

/-- Encode a row-major `n × n` integer matrix fixture as the JSON 2D
array shape FLINT's `fmpz_mat` family accepts (`rows: [[…], …]`). -/
def flatToFlintRows (n : Nat) (entries : Array Int) : Lean.Json :=
  let rows : Array Lean.Json := (Array.range n).map fun i =>
    let row := (Array.range n).map fun j => entries.getD (i * n + j) 0
    Hex.BenchOracle.Flint.intsToJson row.toList
  Lean.Json.arr rows

/-- FLINT comparator: `fmpz_mat.det`. Returns the determinant directly
(matches `runBareissDet` on the same prepared input, modulo Bareiss's
single sign convention from row pivoting versus FLINT's multimodular
result). -/
def runFlintBareissDet (input : DetInput) : IO Int := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mat" "det"
    #[("rows", flatToFlintRows input.n input.entries)]
  match result.getInt? with
  | Except.ok n => return n
  | Except.error msg =>
      throw <| IO.userError s!"FLINT fmpz_mat.det result not integer: {msg}"

/-! Per-rung wrappers for paired fixed-benchmark registrations. Each
`runBareissDetAt n` calls the Hex target on `prepDetInput n`; each
`runFlintBareissDetAt n` calls the FLINT comparator on the same
prepared input so wall-times are comparable in the same harness. -/

def runBareissDetAt (n : Nat) : Unit → IO Int := fun _ =>
  return runBareissDet (prepDetInput n)
def runFlintBareissDetAt (n : Nat) : Unit → IO Int := fun _ =>
  runFlintBareissDet (prepDetInput n)

/-! Per-rung concrete bindings used by `setup_fixed_benchmark`. The
rung ladder densifies the parametric `[8, 12, 16]` schedule outward
toward sizes where FLINT's per-call wall time clears the persistent-
subprocess startup floor, while staying inside the 10 s hard / 1 s
soft per-call ceiling (per `SPEC/benchmarking.md §"Headline reports"
§"Comparator ratios"`). The tridiagonal `flatSmallMatrix` fixture
keeps Bareiss intermediates bounded so the cubic in `n` scales the
elimination loop, not bigint operand growth. -/

def runBareissDet16 : Unit → IO Int := runBareissDetAt 16
def runFlintBareissDet16 : Unit → IO Int := runFlintBareissDetAt 16
def runBareissDet24 : Unit → IO Int := runBareissDetAt 24
def runFlintBareissDet24 : Unit → IO Int := runFlintBareissDetAt 24
def runBareissDet32 : Unit → IO Int := runBareissDetAt 32
def runFlintBareissDet32 : Unit → IO Int := runFlintBareissDetAt 32
def runBareissDet48 : Unit → IO Int := runBareissDetAt 48
def runFlintBareissDet48 : Unit → IO Int := runFlintBareissDetAt 48
def runBareissDet64 : Unit → IO Int := runBareissDetAt 64
def runFlintBareissDet64 : Unit → IO Int := runFlintBareissDetAt 64
def runBareissDet96 : Unit → IO Int := runBareissDetAt 96
def runFlintBareissDet96 : Unit → IO Int := runFlintBareissDetAt 96
def runBareissDet128 : Unit → IO Int := runBareissDetAt 128
def runFlintBareissDet128 : Unit → IO Int := runFlintBareissDetAt 128
def runBareissDet192 : Unit → IO Int := runBareissDetAt 192
def runFlintBareissDet192 : Unit → IO Int := runFlintBareissDetAt 192
def runBareissDet256 : Unit → IO Int := runBareissDetAt 256
def runFlintBareissDet256 : Unit → IO Int := runFlintBareissDetAt 256
def runBareissDet320 : Unit → IO Int := runBareissDetAt 320
def runFlintBareissDet320 : Unit → IO Int := runFlintBareissDetAt 320
def runBareissDet384 : Unit → IO Int := runBareissDetAt 384
def runFlintBareissDet384 : Unit → IO Int := runFlintBareissDetAt 384
def runBareissDet512 : Unit → IO Int := runBareissDetAt 512
def runFlintBareissDet512 : Unit → IO Int := runFlintBareissDetAt 512

setup_benchmark runSquareMulChecksum n => n * n * n
  with prep := prepMulInput
  where {
    paramFloor := 160
    paramCeiling := 256
    paramSchedule := .custom #[160, 192, 224, 256]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
  }

setup_benchmark runBareissDet n => n * n * n
  with prep := prepDetInput
  where {
    paramFloor := 8
    paramCeiling := 16
    paramSchedule := .custom #[8, 12, 16]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 2000000000
  }

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

/-! ## FLINT `fmpz_mat_det` informational comparator fixed registrations

`runBareissDet` is paired with the FLINT `fmpz_mat.det` op via the
shared persistent-subprocess driver. The pairs are registered as
`setup_fixed_benchmark` rungs across a densified ladder so the
headline report records raw and overhead-adjusted ratios at each rung
and a trend across the ladder. The comparator is `informational` per
`SPEC/Libraries/hex-matrix.md §"External comparators"`: no
gating-goal verdict is required; the ratios are recorded for
orientation. -/

setup_fixed_benchmark runBareissDet16 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintBareissDet16 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runBareissDet24 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintBareissDet24 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runBareissDet32 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintBareissDet32 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runBareissDet48 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintBareissDet48 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runBareissDet64 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintBareissDet64 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runBareissDet96 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintBareissDet96 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runBareissDet128 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintBareissDet128 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runBareissDet192 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintBareissDet192 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runBareissDet256 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintBareissDet256 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runBareissDet320 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runFlintBareissDet320 where { repeats := 5, maxSecondsPerCall := 8.0 }
setup_fixed_benchmark runBareissDet384 where { repeats := 5, maxSecondsPerCall := 12.0 }
setup_fixed_benchmark runFlintBareissDet384 where { repeats := 5, maxSecondsPerCall := 12.0 }
setup_fixed_benchmark runBareissDet512 where { repeats := 5, maxSecondsPerCall := 25.0 }
setup_fixed_benchmark runFlintBareissDet512 where { repeats := 5, maxSecondsPerCall := 25.0 }

end Hex.MatrixBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
