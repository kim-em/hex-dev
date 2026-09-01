/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRowReduce
import Hex.BenchOracle.Flint
import Lean.Data.Json
import LeanBench

/-!
Mode-1 benchmarks for every advertised executable `HexRowReduce` operation.

The dense family is `I + J`: every column supplies a pivot while rational
heights remain bounded.  The deficient family repeats the rows and columns of
the half-size dense matrix, giving rank and nullity `n / 2`.  Prepared targets
receive their proved RREF data outside the timed region.
-/

namespace Hex.RowReduceBench

structure Input where
  n : Nat
  matrix : Matrix Rat n n
  query : Vector Rat n

private def vectorChecksum {n : Nat} (v : Vector Rat n) : UInt64 :=
  hash v.toArray

private def matrixChecksum {n m : Nat} (M : Matrix Rat n m) : UInt64 :=
  M.rows.toArray.foldl
    (fun checksum row => mixHash checksum (vectorChecksum row)) (hash n)

instance : Hashable Input where
  hash input := mixHash (hash input.n) <|
    mixHash (matrixChecksum input.matrix) (vectorChecksum input.query)

structure ReducedInput where
  n : Nat
  source : Matrix Rat n n
  data : Matrix.RowEchelonData Rat n n
  reduced : Matrix.IsRowReduced source data
  query : Vector Rat n

instance : Hashable ReducedInput where
  hash input := mixHash (hash input.n) <|
    mixHash (matrixChecksum input.source) <|
      mixHash (matrixChecksum input.data.echelon) <|
        mixHash (matrixChecksum input.data.transform) <|
          mixHash (hash input.data.pivotCols.toArray) (vectorChecksum input.query)

def dense (n : Nat) : Input :=
  let matrix : Matrix Rat n n :=
    Matrix.ofFn fun i j => if i = j then 2 else 1
  let query : Vector Rat n :=
    Vector.ofFn fun j => if j.val = 0 then 2 else 1
  { n, matrix, query }

def deficient (n : Nat) : Input :=
  let rank := n / 2
  let matrix : Matrix Rat n n := Matrix.ofFn fun i j =>
    if rank = 0 then 0
    else if i.val % rank = j.val % rank then 2 else 1
  let query : Vector Rat n := Vector.ofFn fun j =>
    if rank = 0 then 0 else if j.val % rank = 0 then 2 else 1
  { n, matrix, query }

/-- Already-reduced projection used to prepare contract-level targets without
coefficient growth. -/
def reducedDeficient (n : Nat) : Input :=
  let rank := n / 2
  let matrix : Matrix Rat n n := Matrix.ofFn fun i j =>
    if i = j ∧ i.val < rank then 1 else 0
  let query : Vector Rat n := Vector.ofFn fun j =>
    if j.val = 0 ∧ 0 < rank then 1 else 0
  { n, matrix, query }

def denseReduced (n : Nat) : ReducedInput :=
  let input := dense n
  let data := Matrix.rowReduce input.matrix
  { n, source := input.matrix, data
    reduced := Matrix.rowReduce_isRowReduced input.matrix
    query := input.query }

def deficientReduced (n : Nat) : ReducedInput :=
  let input := reducedDeficient n
  let data := Matrix.rowReduce input.matrix
  { n, source := input.matrix, data
    reduced := Matrix.rowReduce_isRowReduced input.matrix
    query := input.query }

def runReduce (input : Input) : UInt64 :=
  let result := Matrix.rowReduce input.matrix
  mixHash (hash result.rank) <|
    mixHash (matrixChecksum result.echelon) <|
      mixHash (matrixChecksum result.transform) (hash result.pivotCols.toArray)

def runRank (input : Input) : Nat :=
  Matrix.rowReduce_rank input.matrix

def runSpanCoeffs (input : Input) : UInt64 :=
  match Matrix.spanCoeffs input.matrix input.query with
  | some coefficients => vectorChecksum coefficients
  | none => 0

def runSpanContains (input : Input) : Bool :=
  Matrix.spanContains input.matrix input.query

def runEchelonSpanCoeffs (input : ReducedInput) : UInt64 :=
  match input.reduced.toIsEchelonForm.spanCoeffs input.query with
  | some coefficients => vectorChecksum coefficients
  | none => 0

def runEchelonSpanContains (input : ReducedInput) : Bool :=
  input.reduced.toIsEchelonForm.spanContains input.query

def runEchelonCoeffs (input : ReducedInput) : UInt64 :=
  vectorChecksum (input.reduced.toIsEchelonForm.echelonCoeffs input.query)

def runFreeCols (input : ReducedInput) : UInt64 :=
  hash input.reduced.toIsEchelonForm.freeCols.toArray

def runNullspaceMatrix (input : Input) : UInt64 :=
  hash (Matrix.nullspaceBasisMatrix input.matrix).data.toArray

def runNullspace (input : Input) : UInt64 :=
  (Matrix.nullspace input.matrix).toArray.foldl
    (fun checksum vector => mixHash checksum (vectorChecksum vector)) (hash input.n)

def runReducedMatrix (input : ReducedInput) : UInt64 :=
  matrixChecksum input.reduced.nullspaceMatrix

def runReducedNullspace (input : ReducedInput) : UInt64 :=
  input.reduced.nullspace.toArray.foldl
    (fun checksum vector => mixHash checksum (vectorChecksum vector)) (hash input.n)

private def cubicSchedule : Array Nat := #[8, 12, 16, 24, 32, 48, 64]
private def spanSchedule : Array Nat := #[16, 24, 32, 48, 64, 96, 128, 192]
-- Use one stable allocation regime per ladder.  The cheap prepared targets
-- use two-second inner batches to clear the default 10× per-spawn signal floor.
private def linearSchedule : Array Nat := #[128, 192, 256, 384, 512]
private def quadraticSchedule : Array Nat := #[128, 192, 256, 384, 512, 768]
private def publicMatrixSchedule : Array Nat := #[48, 56, 64, 72, 80, 96]
private def quadraticVectorSchedule : Array Nat := #[256, 320, 384, 448, 512, 640, 768]

/- Each of the four public wrappers performs dense Gauss--Jordan elimination:
`n` pivots, `n` row updates, and `n` entries per update. -/
-- Cubic: `n` pivots times `n` row updates times `n` entries per update.
setup_benchmark runReduce n => n ^ 3 with prep := dense where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom cubicSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

-- Cubic: rank first performs the same dense Gauss--Jordan elimination.
setup_benchmark runRank n => n ^ 3 with prep := dense where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom cubicSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

-- Cubic: the public wrapper is dominated by dense Gauss--Jordan elimination.
setup_benchmark runSpanCoeffs n => n ^ 3 with prep := dense where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom cubicSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

-- Cubic: the public wrapper is dominated by dense Gauss--Jordan elimination.
setup_benchmark runSpanContains n => n ^ 3 with prep := dense where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom cubicSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

/- Prepared span solving performs a transform-vector product and residual
check, each visiting a square matrix. -/
-- Quadratic: one transform-vector product and one square residual check.
setup_benchmark runEchelonSpanCoeffs n => n ^ 2 with prep := denseReduced where {
  paramFloor := 16, paramCeiling := 192, paramSchedule := .custom spanSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

-- Quadratic: one transform-vector product and one square residual check.
setup_benchmark runEchelonSpanContains n => n ^ 2 with prep := denseReduced where {
  paramFloor := 16, paramCeiling := 192, paramSchedule := .custom spanSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

/- Prepared coefficient selection and the proved sorted-complement merge each
traverse vectors/lists of length proportional to `n`. -/
-- Linear: coefficient selection traverses vectors of length proportional to `n`.
setup_benchmark runEchelonCoeffs n => n with prep := deficientReduced where {
  paramFloor := 128, paramCeiling := 512, paramSchedule := .custom linearSchedule
  targetInnerNanos := 2_000_000_000, outerTrials := 7, maxSecondsPerCall := 10.0
}

-- Linear: the proved sorted-complement merge visits each column once.
setup_benchmark runFreeCols n => n with prep := deficientReduced where {
  paramFloor := 128, paramCeiling := 512, paramSchedule := .custom linearSchedule
  targetInnerNanos := 2_000_000_000, outerTrials := 7, maxSecondsPerCall := 10.0
}

/- Public nullspace wrappers are dominated by the cubic RREF phase; their
rank and nullity are both `n / 2`. -/
-- Cubic: public construction is dominated by RREF before basis materialization.
setup_benchmark runNullspaceMatrix n => n ^ 3 with prep := deficient where {
  paramFloor := 48, paramCeiling := 96, paramSchedule := .custom publicMatrixSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

-- Cubic: public construction is dominated by RREF before basis materialization.
setup_benchmark runNullspace n => n ^ 3 with prep := deficient where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom cubicSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

/- Prepared nullspace constructors materialize `n * (n - r)` entries.  The
column-to-pivot lookup is prepared once, so each output entry is constant-time
apart from rational access/negation. -/
-- Quadratic: materialize `n * (n - r)` entries with `r = n / 2`.
setup_benchmark runReducedMatrix n => n ^ 2 with prep := deficientReduced where {
  paramFloor := 128, paramCeiling := 768, paramSchedule := .custom quadraticSchedule
  targetInnerNanos := 2_000_000_000, outerTrials := 7, maxSecondsPerCall := 10.0
}

-- Quadratic: materialize `n * (n - r)` vector entries with `r = n / 2`.
setup_benchmark runReducedNullspace n => n ^ 2 with prep := deficientReduced where {
  paramFloor := 256, paramCeiling := 768, paramSchedule := .custom quadraticVectorSchedule
  targetInnerNanos := 2_000_000_000, outerTrials := 7, maxSecondsPerCall := 10.0
}

/-! Informational FLINT comparison for the one identical callable result:
rank of dense `I + J`.  Both fixed endpoints return only `Nat`; full RREF and
nullspace values remain conformance-oracle responsibilities. -/

def runRankAt (n : Nat) : Unit → IO Nat :=
  let input := dense n
  fun _ => return runRank input

def runFlintRankAt (n : Nat) (_ : Unit) : IO Nat := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpq_mat" "rank_dense"
    #[("n", Lean.Json.num n)]
  match result.getNat? with
  | Except.ok rank => return rank
  | Except.error msg => throw <| IO.userError s!"FLINT fmpq_mat rank is not natural: {msg}"

def runFlintOverhead (_ : Unit) : IO Nat := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpq_mat" "overhead" #[]
  match result.getNat? with
  | Except.ok value => return value
  | Except.error msg => throw <| IO.userError s!"FLINT fmpq_mat overhead is not natural: {msg}"

def runRank16 := runRankAt 16
def runRank24 := runRankAt 24
def runRank32 := runRankAt 32
def runRank48 := runRankAt 48
def runRank64 := runRankAt 64
def runFlintRank16 := runFlintRankAt 16
def runFlintRank24 := runFlintRankAt 24
def runFlintRank32 := runFlintRankAt 32
def runFlintRank48 := runFlintRankAt 48
def runFlintRank64 := runFlintRankAt 64

def compareConfig (expected : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 10.0, minTotalSeconds := 0.2,
    warmupFirstIter := true, expectedHash := some expected }

setup_fixed_benchmark runFlintOverhead where compareConfig (hash (0 : Nat))
setup_fixed_benchmark runRank16 where compareConfig (hash (16 : Nat))
setup_fixed_benchmark runFlintRank16 where compareConfig (hash (16 : Nat))
setup_fixed_benchmark runRank24 where compareConfig (hash (24 : Nat))
setup_fixed_benchmark runFlintRank24 where compareConfig (hash (24 : Nat))
setup_fixed_benchmark runRank32 where compareConfig (hash (32 : Nat))
setup_fixed_benchmark runFlintRank32 where compareConfig (hash (32 : Nat))
setup_fixed_benchmark runRank48 where compareConfig (hash (48 : Nat))
setup_fixed_benchmark runFlintRank48 where compareConfig (hash (48 : Nat))
setup_fixed_benchmark runRank64 where compareConfig (hash (64 : Nat))
setup_fixed_benchmark runFlintRank64 where compareConfig (hash (64 : Nat))

end Hex.RowReduceBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
