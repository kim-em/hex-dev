/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRowReduce
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
    (hash n)

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
def runEchelonSpanCoeffs (input : ReducedInput) : UInt64 :=
  match input.reduced.toIsEchelonForm.spanCoeffs input.query with
  | some coefficients => vectorChecksum coefficients
  | none => 0

/-- Contract-level row-span membership on prepared RREF data. -/
def runEchelonSpanContains (input : ReducedInput) : Bool :=
  input.reduced.toIsEchelonForm.spanContains input.query

/-- Pivot-coordinate coefficient selection on prepared echelon data. -/
def runEchelonCoeffs (input : ReducedInput) : UInt64 :=
  vectorChecksum (input.reduced.toIsEchelonForm.echelonCoeffs input.query)

/-- Sorted complement of the pivot columns on prepared echelon data. -/
def runFreeCols (input : ReducedInput) : UInt64 :=
  hash input.reduced.toIsEchelonForm.freeCols.toArray

/-- The public nullspace basis-matrix wrapper on a rank-deficient matrix. -/
def runNullspaceMatrix (input : Input) : UInt64 :=
  hash (Matrix.nullspaceBasisMatrix input.matrix).data.toArray

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

private def schedule : Array Nat := #[8, 12, 16, 24, 32, 48, 64]
private def basisMatrixSchedule : Array Nat := #[16, 24, 32, 48, 64]

-- Prepared operations avoid elimination.  The quadratic span traversals clear
-- the algorithmic signal by 192, while the cheap pivot scans in the cubic
-- nullspace constructor need larger matrices before their leading term
-- dominates allocation.
private def preparedSpanSchedule : Array Nat := #[16, 24, 32, 48, 64, 96, 128, 192]
private def preparedNullspaceSchedule : Array Nat := #[128, 192, 256, 384, 512, 768, 1024]
-- Keep the prepared vector operations below the runtime's large-allocation
-- transitions; the batched timings already have ample signal at these sizes.
private def preparedLinearSchedule : Array Nat := #[128, 192, 256, 384, 512, 768]
private def freeColsSchedule : Array Nat := #[64, 96, 128, 192, 256, 384, 512]

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
setup_benchmark runEchelonSpanCoeffs n => n ^ 2 with prep := denseReduced where {
  paramFloor := 16, paramCeiling := 192, paramSchedule := .custom preparedSpanSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 3
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: contract-level `spanContains` projects `isSome`
from the same prepared `spanCoeffs` computation and is therefore
`Theta(n^2)` on this family. -/
setup_benchmark runEchelonSpanContains n => n ^ 2 with prep := denseReduced where {
  paramFloor := 16, paramCeiling := 192, paramSchedule := .custom preparedSpanSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 3
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: `echelonCoeffs` constructs one length-`n` vector.
Each live entry performs constant-time pivot-column and matrix indexing on the
prepared bounded-integer projection, so the family performs `Theta(n)` work. -/
setup_benchmark runEchelonCoeffs n => n with prep := deficientReduced where {
  paramFloor := 128, paramCeiling := 768, paramSchedule := .custom preparedLinearSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5
  slopeTolerance := 0.15
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: `freeCols` filters all `n` columns and tests each
against the sorted pivot vector by a linear list-membership scan.  On the
rank-`n / 2` prepared family the aggregate scan is `Theta(n^2)`. -/
setup_benchmark runFreeCols n => n ^ 2 with prep := deficientReduced where {
  paramFloor := 64, paramCeiling := 512, paramSchedule := .custom freeColsSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5
  slopeTolerance := 0.15
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
  targetInnerNanos := 1_000_000_000, outerTrials := 7
  slopeTolerance := 0.20
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: prepared `nullspace` shares the same basis-matrix
construction and then extracts quadratically many entries as columns, so its
model remains `Theta(n^3)` on the rank-deficient family. -/
setup_benchmark runReducedNullspace n => n ^ 3 with prep := deficientReduced where {
  paramFloor := 128, paramCeiling := 1024, paramSchedule := .custom preparedNullspaceSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 7
  slopeTolerance := 0.20
  signalFloorMultiplier := 1.0
  maxSecondsPerCall := 10.0
}

end Hex.RowReduceBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
