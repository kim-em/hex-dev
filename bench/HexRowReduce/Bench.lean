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
Mode-1 benchmarks for the public executable `HexRowReduce` surface.

The `dense` family uses the matrix `I + J`: every column supplies a pivot and
every pivot eliminates nonzero entries above and below it.  Its inverse has
diagonal entries `n / (n + 1)` and off-diagonal entries `-1 / (n + 1)`, so the
controlled family exercises the complete Gauss--Jordan schedule without
uncontrolled rational coefficient growth.

The `deficient` family repeats the rows and columns of `I + J` at dimension
`n / 2`.  It therefore has rank and nullity `n / 2`, exercises successful and
unsuccessful pivot searches, and materializes a quadratic-size nullspace
basis.  Both families are prepared outside the timed region.
-/

namespace Hex.RowReduceBench

/-- A prepared square rational matrix and a known member of its row span. -/
structure Input where
  n : Nat
  matrix : Matrix Rat n n
  query : Vector Rat n

private def vectorChecksum {n : Nat} (v : Vector Rat n) : UInt64 :=
  hash v.toArray

private def matrixChecksum {n m : Nat} (M : Matrix Rat n m) : UInt64 :=
  M.rows.toArray.foldl
    (fun checksum row => mixHash checksum (vectorChecksum row))
    (hash (n, m))

instance : Hashable Input where
  hash input := mixHash (hash input.n) <|
    mixHash (matrixChecksum input.matrix) (vectorChecksum input.query)

/-- Prepared RREF data for isolating the executable contract-level span and
nullspace constructors from the public wrappers' row-reduction phase. -/
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

/-- Dense `I + J`, whose full Gauss--Jordan path stays at logarithmic
coefficient height. -/
def dense (n : Nat) : Input :=
  let matrix : Matrix Rat n n :=
    Matrix.ofFn fun i j => if i = j then 2 else 1
  let query : Vector Rat n :=
    Vector.ofFn fun j => if j.val = 0 then 2 else 1
  { n, matrix, query }

/-- A dense square matrix obtained by repeating the rows and columns of
`I + J` at dimension `n / 2`. -/
def deficient (n : Nat) : Input :=
  let rank := n / 2
  let matrix : Matrix Rat n n := Matrix.ofFn fun i j =>
    if rank = 0 then 0
    else if i.val % rank = j.val % rank then 2 else 1
  let query : Vector Rat n := Vector.ofFn fun j =>
    if rank = 0 then 0
    else if j.val % rank = 0 then 2 else 1
  { n, matrix, query }

/-- A sparse rank-`n / 2` projection used only to prepare the contract-level
nullspace targets.  Its already-reduced shape keeps untimed witness
construction cheap enough for the larger ladder needed to expose pivot scans.
-/
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

/-- Force every field of the transform-producing RREF result. -/
def runReduce (input : Input) : UInt64 :=
  let result := Matrix.rowReduce input.matrix
  mixHash (hash result.rank) <|
    mixHash (matrixChecksum result.echelon) <|
      mixHash (matrixChecksum result.transform) (hash result.pivotCols.toArray)

/-- Rank projection through the public row-reduction wrapper. -/
def runRank (input : Input) : Nat :=
  Matrix.rowReduce_rank input.matrix

/-- Constructive row-span coefficients for a known member. -/
def runSpanCoeffs (input : Input) : UInt64 :=
  match Matrix.spanCoeffs input.matrix input.query with
  | some coefficients => mixHash (vectorChecksum input.query) (vectorChecksum coefficients)
  | none => 0

/-- Row-span membership for the same known member. -/
def runSpanContains (input : Input) : UInt64 :=
  mixHash (vectorChecksum input.query) (hash (Matrix.spanContains input.matrix input.query))

/-- Contract-level row-span coefficient construction on prepared RREF data. -/
def runEchelonCoeffs (input : ReducedInput) : UInt64 :=
  match input.reduced.toIsEchelonForm.spanCoeffs input.query with
  | some coefficients => vectorChecksum coefficients
  | none => 0

/-- Contract-level row-span membership on prepared RREF data. -/
def runEchelonContains (input : ReducedInput) : Bool :=
  input.reduced.toIsEchelonForm.spanContains input.query

/-- The public nullspace basis-matrix wrapper on a rank-deficient matrix. -/
def runNullspaceMatrix (input : Input) : UInt64 :=
  matrixChecksum (Matrix.nullspaceBasisMatrix input.matrix)

/-- The public vector-of-vectors nullspace wrapper on a rank-deficient matrix. -/
def runNullspace (input : Input) : UInt64 :=
  (Matrix.nullspace input.matrix).toArray.foldl
    (fun checksum vector => mixHash checksum (vectorChecksum vector))
    (hash input.n)

/-- Contract-level nullspace basis matrix on prepared rank-deficient RREF. -/
def runReducedMatrix (input : ReducedInput) : UInt64 :=
  matrixChecksum input.reduced.nullspaceMatrix

/-- Contract-level vector-of-vectors nullspace on prepared rank-deficient RREF. -/
def runReducedNullspace (input : ReducedInput) : UInt64 :=
  input.reduced.nullspace.toArray.foldl
    (fun checksum vector => mixHash checksum (vectorChecksum vector))
    (hash input.n)

private def natJson (value : Nat) : Lean.Json :=
  Lean.Json.num (Lean.JsonNumber.fromNat value)

private def ratJson (value : Rat) : Lean.Json :=
  Lean.Json.arr #[
    Lean.Json.num (Lean.JsonNumber.fromInt value.num),
    Lean.Json.num (Lean.JsonNumber.fromNat value.den)]

private def vectorJson {n : Nat} (vector : Vector Rat n) : Lean.Json :=
  Lean.Json.arr (vector.toArray.map ratJson)

private def matrixJson {n m : Nat} (matrix : Matrix Rat n m) : Lean.Json :=
  Lean.Json.arr (matrix.rows.toArray.map vectorJson)

private def rrefJson (input : Input) : Lean.Json :=
  let result := Matrix.rowReduce input.matrix
  Lean.Json.mkObj [
    ("rank", natJson result.rank),
    ("pivots", Lean.Json.arr (result.pivotCols.toArray.map fun pivot => natJson pivot.val)),
    ("rows", matrixJson result.echelon)]

private def nullspaceJson (input : Input) : Lean.Json :=
  let basis := (Matrix.nullspace input.matrix).toArray
  Lean.Json.mkObj [
    ("rank", natJson (input.n - basis.size)),
    ("basis", Lean.Json.arr (basis.map vectorJson))]

/-- Hex-side fixed comparator endpoint for RREF and rank. -/
def runHexRrefAt (n : Nat) : Unit → IO String := fun _ =>
  return (rrefJson (dense n)).compress

/-- python-flint `fmpq_mat.rref` endpoint on the same dense fixture. -/
def runFlintRrefAt (n : Nat) : Unit → IO String := fun _ => do
  let input := dense n
  let result ← Hex.BenchOracle.Flint.runOp "fmpq_mat" "rref"
    #[("rows", matrixJson input.matrix)]
  return result.compress

/-- Hex-side fixed comparator endpoint for the canonical nullspace basis. -/
def runHexNullspaceAt (n : Nat) : Unit → IO String := fun _ =>
  return (nullspaceJson (deficient n)).compress

/-- python-flint RREF-derived nullspace endpoint on the same deficient fixture. -/
def runFlintNullspaceAt (n : Nat) : Unit → IO String := fun _ => do
  let input := deficient n
  let result ← Hex.BenchOracle.Flint.runOp "fmpq_mat" "nullspace"
    #[("rows", matrixJson input.matrix)]
  return result.compress

/-- Persistent-protocol overhead control: no matrix construction or FLINT
operation. -/
def runFlintOverhead (_ : Unit) : IO String := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpq_mat" "overhead" #[]
  return result.compress

def runHexRref8 : Unit → IO String := runHexRrefAt 8
def runFlintRref8 : Unit → IO String := runFlintRrefAt 8
def runHexRref12 : Unit → IO String := runHexRrefAt 12
def runFlintRref12 : Unit → IO String := runFlintRrefAt 12
def runHexRref16 : Unit → IO String := runHexRrefAt 16
def runFlintRref16 : Unit → IO String := runFlintRrefAt 16
def runHexRref24 : Unit → IO String := runHexRrefAt 24
def runFlintRref24 : Unit → IO String := runFlintRrefAt 24
def runHexRref32 : Unit → IO String := runHexRrefAt 32
def runFlintRref32 : Unit → IO String := runFlintRrefAt 32
def runHexRref48 : Unit → IO String := runHexRrefAt 48
def runFlintRref48 : Unit → IO String := runFlintRrefAt 48
def runHexRref64 : Unit → IO String := runHexRrefAt 64
def runFlintRref64 : Unit → IO String := runFlintRrefAt 64

def runHexNullspace8 : Unit → IO String := runHexNullspaceAt 8
def runFlintNullspace8 : Unit → IO String := runFlintNullspaceAt 8
def runHexNullspace12 : Unit → IO String := runHexNullspaceAt 12
def runFlintNullspace12 : Unit → IO String := runFlintNullspaceAt 12
def runHexNullspace16 : Unit → IO String := runHexNullspaceAt 16
def runFlintNullspace16 : Unit → IO String := runFlintNullspaceAt 16
def runHexNullspace24 : Unit → IO String := runHexNullspaceAt 24
def runFlintNullspace24 : Unit → IO String := runFlintNullspaceAt 24
def runHexNullspace32 : Unit → IO String := runHexNullspaceAt 32
def runFlintNullspace32 : Unit → IO String := runFlintNullspaceAt 32
def runHexNullspace48 : Unit → IO String := runHexNullspaceAt 48
def runFlintNullspace48 : Unit → IO String := runFlintNullspaceAt 48
def runHexNullspace64 : Unit → IO String := runHexNullspaceAt 64
def runFlintNullspace64 : Unit → IO String := runFlintNullspaceAt 64

private def schedule : Array Nat := #[8, 12, 16, 24, 32, 48, 64]
private def basisMatrixSchedule : Array Nat := #[16, 24, 32, 48, 64]

-- Prepared operations avoid elimination.  The quadratic span traversals clear
-- the algorithmic signal by 192, while the cheap pivot scans in the cubic
-- nullspace constructor need larger matrices before their leading term
-- dominates allocation.
private def preparedSpanSchedule : Array Nat := #[16, 24, 32, 48, 64, 96, 128, 192]
private def preparedNullspaceSchedule : Array Nat := #[128, 192, 256, 384, 512, 768, 1024]

/- Cost-model derivation: on dense `I + J`, all `n` pivots fire.  Each pivot
normalizes two length-`n` rows (echelon and transform) and eliminates up to
`n - 1` nonzero rows in both matrices, hence `Theta(n^3)` field operations.
The family keeps rational numerators and denominators `O(n)`, so every operand
fits one machine word on this schedule and the independently derived wall
model is `n^3`. -/
setup_benchmark runReduce n => n ^ 3 with prep := dense where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom schedule
  targetInnerNanos := 1_000_000_000, outerTrials := 3
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: `rowReduce_rank` projects one field from the same
complete dense RREF run, so its controlled-family model remains `Theta(n^3)`.
-/
setup_benchmark runRank n => n ^ 3 with prep := dense where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom schedule
  targetInnerNanos := 1_000_000_000, outerTrials := 3
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: `spanCoeffs` performs the same cubic dense RREF run,
then one transform-vector product and one residual row-combination check, both
quadratic.  The resulting controlled-family model is therefore `Theta(n^3)`.
-/
setup_benchmark runSpanCoeffs n => n ^ 3 with prep := dense where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom schedule
  targetInnerNanos := 1_000_000_000, outerTrials := 3
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: `spanContains` is the `Option.isSome` projection of
the same `spanCoeffs` computation, preserving its `Theta(n^3)` model. -/
setup_benchmark runSpanContains n => n ^ 3 with prep := dense where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom schedule
  targetInnerNanos := 1_000_000_000, outerTrials := 3
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: on prepared full-rank RREF data, `spanCoeffs` makes
one dense transform-vector product and one residual row-combination check.
Both visit `Theta(n^2)` entries; coefficient selection is linear. -/
setup_benchmark runEchelonCoeffs n => n ^ 2 with prep := denseReduced where {
  paramFloor := 16, paramCeiling := 192, paramSchedule := .custom preparedSpanSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 3
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: contract-level `spanContains` projects `isSome`
from the same prepared `spanCoeffs` computation and is therefore
`Theta(n^2)` on this family. -/
setup_benchmark runEchelonContains n => n ^ 2 with prep := denseReduced where {
  paramFloor := 16, paramCeiling := 192, paramSchedule := .custom preparedSpanSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 3
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: the deficient family has rank and nullity `n / 2`.
Its RREF phase is cubic, and `nullspaceMatrix` constructs `Theta(n^2)` entries
whose pivot lookup scans at most `n / 2` pivot columns, also `Theta(n^3)`.
The ladder begins at 16, where forcing the basis matrix has entered that
derived dominant regime.
-/
setup_benchmark runNullspaceMatrix n => n ^ 3 with prep := deficient where {
  paramFloor := 16, paramCeiling := 64, paramSchedule := .custom basisMatrixSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 3
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: `nullspace` shares one basis-matrix construction and
extracts its `n / 2` length-`n` columns.  That quadratic projection follows
the same cubic RREF and pivot-lookup work as `nullspaceBasisMatrix`, so the
controlled-family model remains `Theta(n^3)`. -/
setup_benchmark runNullspace n => n ^ 3 with prep := deficient where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom schedule
  targetInnerNanos := 1_000_000_000, outerTrials := 3
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: prepared `nullspaceMatrix` constructs
`Theta(n^2)` entries on rank/nullity `n / 2`; pivot entries perform a linear
scan through at most `n / 2` pivot columns, yielding `Theta(n^3)` work. -/
setup_benchmark runReducedMatrix n => n ^ 3 with prep := deficientReduced where {
  paramFloor := 128, paramCeiling := 1024, paramSchedule := .custom preparedNullspaceSchedule
  targetInnerNanos := 200_000_000, outerTrials := 7
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: prepared `nullspace` shares the same basis-matrix
construction and then extracts quadratically many entries as columns, so its
model remains `Theta(n^3)` on the rank-deficient family. -/
setup_benchmark runReducedNullspace n => n ^ 3 with prep := deficientReduced where {
  paramFloor := 128, paramCeiling := 1024, paramSchedule := .custom preparedNullspaceSchedule
  targetInnerNanos := 200_000_000, outerTrials := 7
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/-! The fixed registrations below are comparator and protocol anchors only;
they make no complexity claim and do not replace the ten mode-1 registrations
above.  Each Hex/python-flint pair returns the same canonical JSON string, so
LeanBench's result hash checks exact RREF or nullspace-basis agreement at every
shared rung. -/

private def hexComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  minTotalSeconds := 0.1
  maxSecondsPerCall := 8.0

private def flintComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  minTotalSeconds := 0.1
  maxSecondsPerCall := 8.0
  warmupFirstIter := true

setup_fixed_benchmark runFlintOverhead where
  { flintComparisonConfig with expectedHash := some 0x84d361908b60d650 }
setup_fixed_benchmark runHexRref8 where
  { hexComparisonConfig with expectedHash := some 0x6ca6178de0126e10 }
setup_fixed_benchmark runFlintRref8 where
  { flintComparisonConfig with expectedHash := some 0x6ca6178de0126e10 }
setup_fixed_benchmark runHexRref12 where
  { hexComparisonConfig with expectedHash := some 0x3548b1dee30b7444 }
setup_fixed_benchmark runFlintRref12 where
  { flintComparisonConfig with expectedHash := some 0x3548b1dee30b7444 }
setup_fixed_benchmark runHexRref16 where
  { hexComparisonConfig with expectedHash := some 0xd6434cb7f79aa670 }
setup_fixed_benchmark runFlintRref16 where
  { flintComparisonConfig with expectedHash := some 0xd6434cb7f79aa670 }
setup_fixed_benchmark runHexRref24 where
  { hexComparisonConfig with expectedHash := some 0xab53897f9681f1ce }
setup_fixed_benchmark runFlintRref24 where
  { flintComparisonConfig with expectedHash := some 0xab53897f9681f1ce }
setup_fixed_benchmark runHexRref32 where
  { hexComparisonConfig with expectedHash := some 0x69bb3c6679a2cc4b }
setup_fixed_benchmark runFlintRref32 where
  { flintComparisonConfig with expectedHash := some 0x69bb3c6679a2cc4b }
setup_fixed_benchmark runHexRref48 where
  { hexComparisonConfig with expectedHash := some 0xa23e2013cacf6e4e }
setup_fixed_benchmark runFlintRref48 where
  { flintComparisonConfig with expectedHash := some 0xa23e2013cacf6e4e }
setup_fixed_benchmark runHexRref64 where
  { hexComparisonConfig with expectedHash := some 0x91317157ea95e9af }
setup_fixed_benchmark runFlintRref64 where
  { flintComparisonConfig with expectedHash := some 0x91317157ea95e9af }
setup_fixed_benchmark runHexNullspace8 where
  { hexComparisonConfig with expectedHash := some 0xd2e37217fbfa8544 }
setup_fixed_benchmark runFlintNullspace8 where
  { flintComparisonConfig with expectedHash := some 0xd2e37217fbfa8544 }
setup_fixed_benchmark runHexNullspace12 where
  { hexComparisonConfig with expectedHash := some 0x35220a3c9f4587fe }
setup_fixed_benchmark runFlintNullspace12 where
  { flintComparisonConfig with expectedHash := some 0x35220a3c9f4587fe }
setup_fixed_benchmark runHexNullspace16 where
  { hexComparisonConfig with expectedHash := some 0x0003b3f1256cc8a8 }
setup_fixed_benchmark runFlintNullspace16 where
  { flintComparisonConfig with expectedHash := some 0x0003b3f1256cc8a8 }
setup_fixed_benchmark runHexNullspace24 where
  { hexComparisonConfig with expectedHash := some 0xd57d96c775400424 }
setup_fixed_benchmark runFlintNullspace24 where
  { flintComparisonConfig with expectedHash := some 0xd57d96c775400424 }
setup_fixed_benchmark runHexNullspace32 where
  { hexComparisonConfig with expectedHash := some 0xe59fa635b61f86d7 }
setup_fixed_benchmark runFlintNullspace32 where
  { flintComparisonConfig with expectedHash := some 0xe59fa635b61f86d7 }
setup_fixed_benchmark runHexNullspace48 where
  { hexComparisonConfig with expectedHash := some 0x5c4539422fa584e4 }
setup_fixed_benchmark runFlintNullspace48 where
  { flintComparisonConfig with expectedHash := some 0x5c4539422fa584e4 }
setup_fixed_benchmark runHexNullspace64 where
  { hexComparisonConfig with expectedHash := some 0x60ac962101f19bc3 }
setup_fixed_benchmark runFlintNullspace64 where
  { flintComparisonConfig with expectedHash := some 0x60ac962101f19bc3 }

end Hex.RowReduceBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
