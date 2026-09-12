/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRowReduce
import HexPolyFp.PrimeField
import HexRationalFn
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
private def quadraticVectorSchedule : Array Nat := #[256, 320, 384, 448, 512, 640, 768]

/- Each of the four public wrappers performs dense Gauss--Jordan elimination:
`n` pivots, `n` row updates, and `n` entries per update. -/
-- Cubic: `n` pivots times `n` row updates times `n` entries per update.
setup_benchmark runReduce n => n ^ 3 with prep := Hex.RowReduceBench.dense where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom cubicSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

-- Cubic: rank first performs the same dense Gauss--Jordan elimination.
setup_benchmark runRank n => n ^ 3 with prep := Hex.RowReduceBench.dense where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom cubicSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

-- Cubic: the public wrapper is dominated by dense Gauss--Jordan elimination.
setup_benchmark runSpanCoeffs n => n ^ 3 with prep := Hex.RowReduceBench.dense where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom cubicSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

-- Cubic: the public wrapper is dominated by dense Gauss--Jordan elimination.
setup_benchmark runSpanContains n => n ^ 3 with prep := Hex.RowReduceBench.dense where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom cubicSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

/- Prepared span solving performs a transform-vector product and residual
check, each visiting a square matrix. -/
-- Quadratic: one transform-vector product and one square residual check.
setup_benchmark runEchelonSpanCoeffs n => n ^ 2 with prep := Hex.RowReduceBench.denseReduced where {
  paramFloor := 16, paramCeiling := 192, paramSchedule := .custom spanSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

-- Quadratic: one transform-vector product and one square residual check.
setup_benchmark runEchelonSpanContains n => n ^ 2 with prep := Hex.RowReduceBench.denseReduced where {
  paramFloor := 16, paramCeiling := 192, paramSchedule := .custom spanSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

/- Prepared coefficient selection and the proved sorted-complement merge each
traverse vectors/lists of length proportional to `n`. -/
-- Linear: coefficient selection traverses vectors of length proportional to `n`.
setup_benchmark runEchelonCoeffs n => n with prep := Hex.RowReduceBench.deficientReduced where {
  paramFloor := 128, paramCeiling := 512, paramSchedule := .custom linearSchedule
  targetInnerNanos := 2_000_000_000, outerTrials := 7, maxSecondsPerCall := 10.0
}

-- Linear: the proved sorted-complement merge visits each column once.
setup_benchmark runFreeCols n => n with prep := Hex.RowReduceBench.deficientReduced where {
  paramFloor := 128, paramCeiling := 512, paramSchedule := .custom linearSchedule
  targetInnerNanos := 2_000_000_000, outerTrials := 7, maxSecondsPerCall := 10.0
}

/- Public nullspace wrappers are dominated by the cubic RREF phase; their
rank and nullity are both `n / 2`. -/
-- Cubic: public construction is dominated by RREF before basis materialization.
setup_benchmark runNullspaceMatrix n => n ^ 3 with prep := Hex.RowReduceBench.deficient where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom cubicSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

-- Cubic: public construction is dominated by RREF before basis materialization.
setup_benchmark runNullspace n => n ^ 3 with prep := Hex.RowReduceBench.deficient where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom cubicSchedule
  targetInnerNanos := 1_000_000_000, outerTrials := 5, maxSecondsPerCall := 10.0
}

/- Prepared nullspace constructors materialize `n * (n - r)` entries.  The
column-to-pivot lookup is prepared once, so each output entry is constant-time
apart from rational access/negation. -/
-- Quadratic: materialize `n * (n - r)` entries with `r = n / 2`.
setup_benchmark runReducedMatrix n => n ^ 2 with prep := Hex.RowReduceBench.deficientReduced where {
  paramFloor := 128, paramCeiling := 768, paramSchedule := .custom quadraticSchedule
  targetInnerNanos := 2_000_000_000, outerTrials := 7, maxSecondsPerCall := 10.0
}

-- Quadratic: materialize `n * (n - r)` vector entries with `r = n / 2`.
setup_benchmark runReducedNullspace n => n ^ 2 with prep := Hex.RowReduceBench.deficientReduced where {
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

namespace Field
open Lean

/-- Prepared field system; rank and consistency are checked before timing. -/
structure Input (F : Type) where
  n : Nat
  m : Nat
  rank : Nat
  A : Matrix F n m
  b : Vector F n
  checksum : F → UInt64

instance [OfNat F 0] : Inhabited (Input F) :=
  ⟨⟨0, 0, 0, 0, 0, fun _ => 0⟩⟩

private def vecHash (f : F → UInt64) (x : Vector F n) : UInt64 :=
  x.toArray.foldl (fun h a => mixHash h (f a)) 0
private def matHash (f : F → UInt64) (A : Matrix F n m) : UInt64 :=
  -- Recover the width from storage: evaluating a dependent `m - rank A`
  -- argument here would run a second elimination just to hash its dimension.
  let data := A.data.toArray
  data.foldl (fun h a => mixHash h (f a)) (mixHash (hash n) (hash (data.size / n)))

instance : Hashable (Input F) where
  hash x := mixHash (hash x.rank) (mixHash (matHash x.checksum x.A) (vecHash x.checksum x.b))

private def inverse [Lean.Grind.Field F] [DecidableEq F] (x : Input F) : UInt64 :=
  if h : x.m = x.n then
    match Matrix.inverse? (h ▸ x.A) with
    | none => 0
    | some B => matHash x.checksum B
  else panic! "inverse benchmark requires square input"

private def solve [Lean.Grind.Field F] [DecidableEq F] (x : Input F) : UInt64 :=
  match Matrix.solve x.A x.b with
  | .error y => vecHash x.checksum y
  | .ok (v, N) => mixHash (vecHash x.checksum v) (matHash x.checksum N)

private def solveOption [Lean.Grind.Field F] [DecidableEq F] (x : Input F) : UInt64 :=
  match Matrix.solve? x.A x.b with
  | none => 0
  | some (v, N) => mixHash (vecHash x.checksum v) (matHash x.checksum N)

/-- A seeded rank-one perturbation of identity, extended by repeated rows and
columns. The common denominator controls coefficient growth while all pivot
stages still perform dense elimination. Families 0/1/2 have full, n-1, n/2
rank; 3/4 are the inconsistent variants; 5/6 are tall/wide. -/
private def prepare [Lean.Grind.Field F] [DecidableEq F] (n family : Nat)
    (u v : Nat → F) (checksum : F → UInt64) : Input F := Id.run do
  let n := max 2 n
  let r := if family == 1 || family == 3 then n - 1
    else if family == 2 || family == 4 then n / 2 else n
  let rows := if family == 5 then 2*n else n
  let cols := if family == 6 then 2*n else n
  let A : Matrix F rows cols := Matrix.ofFn fun i j =>
    (if i.val % r = j.val % r then 1 else 0) + u (i.val % r) * v (j.val % r)
  let consistent := A * (Vector.ofFn (fun _ => (1 : F)) : Vector F cols)
  let bad := family == 3 || family == 4
  let b := Vector.ofFn fun i => consistent[i] + (if bad && i.val + 1 == rows then 1 else 0)
  let augmented : Matrix F rows (cols + 1) := Matrix.ofFn fun i j =>
    if h : j.val < cols then A[(i, (⟨j.val, h⟩ : Fin cols))] else b[i]
  if Matrix.rowReduce_rank A != r || Matrix.rowReduce_rank augmented != r + (if bad then 1 else 0) then
    panic! "field benchmark rank or consistency construction failed"
  else return ⟨rows, cols, r, A, b, checksum⟩

private def seeded (bits i : Nat) : Nat :=
  ((List.range ((bits + 31) / 32)).foldl (fun z j =>
    z * 2^32 + (1664525 * (10222 + 17*i + j) + 1013904223) % 2^32) 0) % 2^bits

private def rational (h n family : Nat) : Input Rat :=
  let h := max 8 h
  let d := 2^(h-1) + 1
  prepare n family
    (fun i => (Rat.ofInt (Int.ofNat (2^(h-1) + seeded (h-1) i))) / Rat.ofInt (Int.ofNat d))
    (fun j => Rat.ofInt (Int.ofNat (1 + seeded 3 (j+31)))) hash

scoped instance : ZMod64.Bounds 101 := ⟨by decide, by decide⟩
scoped instance : ZMod64.PrimeModulus 101 := ZMod64.primeModulusOfPrime (by decide)

private def modular (n family : Nat) : Input (ZMod64 101) :=
  let n := max 2 n
  let r := if family == 1 || family == 3 then n - 1
    else if family == 2 || family == 4 then n / 2 else n
  let u := fun i => (1 + seeded 16 i % 100 : Nat)
  let total : ZMod64 101 := (List.range (r-1)).foldl (fun s i => s + u i) 0
  let v := fun j => if j + 1 == r then -total / (u j : ZMod64 101) else 1
  prepare n family (fun i => (u i : ZMod64 101)) v (fun x => hash x.toNat)

private def functionHash (f : RationalFn Rat) : UInt64 :=
  mixHash (hash f.num.toArray) (hash f.den.toArray)

private def functions (n family : Nat) : Input (RationalFn Rat) :=
  let t : RationalFn Rat := RationalFn.X
  let u := fun i => (RationalFn.C (Rat.ofInt (128 + Int.ofNat (seeded 7 i))) * t + 1) / (t + 1)
  prepare n family u (fun j => RationalFn.C (Rat.ofInt (1 + Int.ofNat (seeded 3 (j+31))))) functionHash

private def dimConfig (schedule : Array Nat) : LeanBench.BenchmarkConfig :=
  { paramSchedule := .custom schedule, paramFloor := schedule[0]!,
    paramCeiling := schedule.back!, targetInnerNanos := 200_000_000,
    outerTrials := 3, maxSecondsPerCall := 30.0,
    -- Fixed SPEC ladders with warm child-side repeats; see SPEC/benchmarking.md.
    signalFloorMultiplier := 1.0 }

private def dimensions := #[4, 8, 16, 32, 64]
private def heights := #[8, 16, 32, 64, 128, 256]
private def functionDimensions := #[2, 4, 8]

/- The harness's verify inputs 0 and 1 select dimension 2 or height 8 in
preparation. Scientific schedule values pass through unchanged. -/

def rat8FullInput (n : Nat) : Input (Rat) := rational 8 n 0
def rat8FullSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8FullSolve n => n ^ 3 with prep := rat8FullInput
  where dimConfig dimensions
def rat8FullOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8FullOption n => n ^ 3 with prep := rat8FullInput
  where dimConfig dimensions
def rat8FullInverse (x : Input (Rat)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8FullInverse n => n ^ 3 with prep := rat8FullInput
  where dimConfig dimensions

def rat8DeficientInput (n : Nat) : Input (Rat) := rational 8 n 1
def rat8DeficientSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8DeficientSolve n => n ^ 3 with prep := rat8DeficientInput
  where dimConfig dimensions
def rat8DeficientOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8DeficientOption n => n ^ 3 with prep := rat8DeficientInput
  where dimConfig dimensions
def rat8DeficientInverse (x : Input (Rat)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8DeficientInverse n => n ^ 3 with prep := rat8DeficientInput
  where dimConfig dimensions

def rat8HalfInput (n : Nat) : Input (Rat) := rational 8 n 2
def rat8HalfSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8HalfSolve n => n ^ 3 with prep := rat8HalfInput
  where dimConfig dimensions
def rat8HalfOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8HalfOption n => n ^ 3 with prep := rat8HalfInput
  where dimConfig dimensions
def rat8HalfInverse (x : Input (Rat)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8HalfInverse n => n ^ 3 with prep := rat8HalfInput
  where dimConfig dimensions

def rat8DeficientErrorInput (n : Nat) : Input (Rat) := rational 8 n 3
def rat8DeficientErrorSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8DeficientErrorSolve n => n ^ 3 with prep := rat8DeficientErrorInput
  where dimConfig dimensions
def rat8DeficientErrorOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8DeficientErrorOption n => n ^ 3 with prep := rat8DeficientErrorInput
  where dimConfig dimensions

def rat8HalfErrorInput (n : Nat) : Input (Rat) := rational 8 n 4
def rat8HalfErrorSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8HalfErrorSolve n => n ^ 3 with prep := rat8HalfErrorInput
  where dimConfig dimensions
def rat8HalfErrorOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8HalfErrorOption n => n ^ 3 with prep := rat8HalfErrorInput
  where dimConfig dimensions

def rat8TallInput (n : Nat) : Input (Rat) := rational 8 n 5
def rat8TallSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8TallSolve n => n ^ 3 with prep := rat8TallInput
  where dimConfig dimensions
def rat8TallOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8TallOption n => n ^ 3 with prep := rat8TallInput
  where dimConfig dimensions

def rat8WideInput (n : Nat) : Input (Rat) := rational 8 n 6
def rat8WideSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8WideSolve n => n ^ 3 with prep := rat8WideInput
  where dimConfig dimensions
def rat8WideOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat8WideOption n => n ^ 3 with prep := rat8WideInput
  where dimConfig dimensions

def rat32FullInput (n : Nat) : Input (Rat) := rational 32 n 0
def rat32FullSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32FullSolve n => n ^ 3 with prep := rat32FullInput
  where dimConfig dimensions
def rat32FullOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32FullOption n => n ^ 3 with prep := rat32FullInput
  where dimConfig dimensions
def rat32FullInverse (x : Input (Rat)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32FullInverse n => n ^ 3 with prep := rat32FullInput
  where dimConfig dimensions

def rat32DeficientInput (n : Nat) : Input (Rat) := rational 32 n 1
def rat32DeficientSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32DeficientSolve n => n ^ 3 with prep := rat32DeficientInput
  where dimConfig dimensions
def rat32DeficientOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32DeficientOption n => n ^ 3 with prep := rat32DeficientInput
  where dimConfig dimensions
def rat32DeficientInverse (x : Input (Rat)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32DeficientInverse n => n ^ 3 with prep := rat32DeficientInput
  where dimConfig dimensions

def rat32HalfInput (n : Nat) : Input (Rat) := rational 32 n 2
def rat32HalfSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32HalfSolve n => n ^ 3 with prep := rat32HalfInput
  where dimConfig dimensions
def rat32HalfOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32HalfOption n => n ^ 3 with prep := rat32HalfInput
  where dimConfig dimensions
def rat32HalfInverse (x : Input (Rat)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32HalfInverse n => n ^ 3 with prep := rat32HalfInput
  where dimConfig dimensions

def rat32DeficientErrorInput (n : Nat) : Input (Rat) := rational 32 n 3
def rat32DeficientErrorSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32DeficientErrorSolve n => n ^ 3 with prep := rat32DeficientErrorInput
  where dimConfig dimensions
def rat32DeficientErrorOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32DeficientErrorOption n => n ^ 3 with prep := rat32DeficientErrorInput
  where dimConfig dimensions

def rat32HalfErrorInput (n : Nat) : Input (Rat) := rational 32 n 4
def rat32HalfErrorSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32HalfErrorSolve n => n ^ 3 with prep := rat32HalfErrorInput
  where dimConfig dimensions
def rat32HalfErrorOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32HalfErrorOption n => n ^ 3 with prep := rat32HalfErrorInput
  where dimConfig dimensions

def rat32TallInput (n : Nat) : Input (Rat) := rational 32 n 5
def rat32TallSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32TallSolve n => n ^ 3 with prep := rat32TallInput
  where dimConfig dimensions
def rat32TallOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32TallOption n => n ^ 3 with prep := rat32TallInput
  where dimConfig dimensions

def rat32WideInput (n : Nat) : Input (Rat) := rational 32 n 6
def rat32WideSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32WideSolve n => n ^ 3 with prep := rat32WideInput
  where dimConfig dimensions
def rat32WideOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat32WideOption n => n ^ 3 with prep := rat32WideInput
  where dimConfig dimensions

def rat128FullInput (n : Nat) : Input (Rat) := rational 128 n 0
def rat128FullSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128FullSolve n => n ^ 3 with prep := rat128FullInput
  where dimConfig dimensions
def rat128FullOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128FullOption n => n ^ 3 with prep := rat128FullInput
  where dimConfig dimensions
def rat128FullInverse (x : Input (Rat)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128FullInverse n => n ^ 3 with prep := rat128FullInput
  where dimConfig dimensions

def rat128DeficientInput (n : Nat) : Input (Rat) := rational 128 n 1
def rat128DeficientSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128DeficientSolve n => n ^ 3 with prep := rat128DeficientInput
  where dimConfig dimensions
def rat128DeficientOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128DeficientOption n => n ^ 3 with prep := rat128DeficientInput
  where dimConfig dimensions
def rat128DeficientInverse (x : Input (Rat)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128DeficientInverse n => n ^ 3 with prep := rat128DeficientInput
  where dimConfig dimensions

def rat128HalfInput (n : Nat) : Input (Rat) := rational 128 n 2
def rat128HalfSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128HalfSolve n => n ^ 3 with prep := rat128HalfInput
  where dimConfig dimensions
def rat128HalfOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128HalfOption n => n ^ 3 with prep := rat128HalfInput
  where dimConfig dimensions
def rat128HalfInverse (x : Input (Rat)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128HalfInverse n => n ^ 3 with prep := rat128HalfInput
  where dimConfig dimensions

def rat128DeficientErrorInput (n : Nat) : Input (Rat) := rational 128 n 3
def rat128DeficientErrorSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128DeficientErrorSolve n => n ^ 3 with prep := rat128DeficientErrorInput
  where dimConfig dimensions
def rat128DeficientErrorOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128DeficientErrorOption n => n ^ 3 with prep := rat128DeficientErrorInput
  where dimConfig dimensions

def rat128HalfErrorInput (n : Nat) : Input (Rat) := rational 128 n 4
def rat128HalfErrorSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128HalfErrorSolve n => n ^ 3 with prep := rat128HalfErrorInput
  where dimConfig dimensions
def rat128HalfErrorOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128HalfErrorOption n => n ^ 3 with prep := rat128HalfErrorInput
  where dimConfig dimensions

def rat128TallInput (n : Nat) : Input (Rat) := rational 128 n 5
def rat128TallSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128TallSolve n => n ^ 3 with prep := rat128TallInput
  where dimConfig dimensions
def rat128TallOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128TallOption n => n ^ 3 with prep := rat128TallInput
  where dimConfig dimensions

def rat128WideInput (n : Nat) : Input (Rat) := rational 128 n 6
def rat128WideSolve (x : Input (Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128WideSolve n => n ^ 3 with prep := rat128WideInput
  where dimConfig dimensions
def rat128WideOption (x : Input (Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark rat128WideOption n => n ^ 3 with prep := rat128WideInput
  where dimConfig dimensions

def modularFullInput (n : Nat) : Input (ZMod64 101) := modular n 0
def modularFullSolve (x : Input (ZMod64 101)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularFullSolve n => n ^ 3 with prep := modularFullInput
  where dimConfig dimensions
def modularFullOption (x : Input (ZMod64 101)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularFullOption n => n ^ 3 with prep := modularFullInput
  where dimConfig dimensions
def modularFullInverse (x : Input (ZMod64 101)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularFullInverse n => n ^ 3 with prep := modularFullInput
  where dimConfig dimensions

def modularDeficientInput (n : Nat) : Input (ZMod64 101) := modular n 1
def modularDeficientSolve (x : Input (ZMod64 101)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularDeficientSolve n => n ^ 3 with prep := modularDeficientInput
  where dimConfig dimensions
def modularDeficientOption (x : Input (ZMod64 101)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularDeficientOption n => n ^ 3 with prep := modularDeficientInput
  where dimConfig dimensions
def modularDeficientInverse (x : Input (ZMod64 101)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularDeficientInverse n => n ^ 3 with prep := modularDeficientInput
  where dimConfig dimensions

def modularHalfInput (n : Nat) : Input (ZMod64 101) := modular n 2
def modularHalfSolve (x : Input (ZMod64 101)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularHalfSolve n => n ^ 3 with prep := modularHalfInput
  where dimConfig dimensions
def modularHalfOption (x : Input (ZMod64 101)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularHalfOption n => n ^ 3 with prep := modularHalfInput
  where dimConfig dimensions
def modularHalfInverse (x : Input (ZMod64 101)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularHalfInverse n => n ^ 3 with prep := modularHalfInput
  where dimConfig dimensions

def modularDeficientErrorInput (n : Nat) : Input (ZMod64 101) := modular n 3
def modularDeficientErrorSolve (x : Input (ZMod64 101)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularDeficientErrorSolve n => n ^ 3 with prep := modularDeficientErrorInput
  where dimConfig dimensions
def modularDeficientErrorOption (x : Input (ZMod64 101)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularDeficientErrorOption n => n ^ 3 with prep := modularDeficientErrorInput
  where dimConfig dimensions

def modularHalfErrorInput (n : Nat) : Input (ZMod64 101) := modular n 4
def modularHalfErrorSolve (x : Input (ZMod64 101)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularHalfErrorSolve n => n ^ 3 with prep := modularHalfErrorInput
  where dimConfig dimensions
def modularHalfErrorOption (x : Input (ZMod64 101)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularHalfErrorOption n => n ^ 3 with prep := modularHalfErrorInput
  where dimConfig dimensions

def modularTallInput (n : Nat) : Input (ZMod64 101) := modular n 5
def modularTallSolve (x : Input (ZMod64 101)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularTallSolve n => n ^ 3 with prep := modularTallInput
  where dimConfig dimensions
def modularTallOption (x : Input (ZMod64 101)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularTallOption n => n ^ 3 with prep := modularTallInput
  where dimConfig dimensions

def modularWideInput (n : Nat) : Input (ZMod64 101) := modular n 6
def modularWideSolve (x : Input (ZMod64 101)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularWideSolve n => n ^ 3 with prep := modularWideInput
  where dimConfig dimensions
def modularWideOption (x : Input (ZMod64 101)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark modularWideOption n => n ^ 3 with prep := modularWideInput
  where dimConfig dimensions

def functionsFullInput (n : Nat) : Input (RationalFn Rat) := functions n 0
def functionsFullSolve (x : Input (RationalFn Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsFullSolve n => n ^ 3 with prep := functionsFullInput
  where dimConfig functionDimensions
def functionsFullOption (x : Input (RationalFn Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsFullOption n => n ^ 3 with prep := functionsFullInput
  where dimConfig functionDimensions
def functionsFullInverse (x : Input (RationalFn Rat)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsFullInverse n => n ^ 3 with prep := functionsFullInput
  where dimConfig functionDimensions

def functionsDeficientInput (n : Nat) : Input (RationalFn Rat) := functions n 1
def functionsDeficientSolve (x : Input (RationalFn Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsDeficientSolve n => n ^ 3 with prep := functionsDeficientInput
  where dimConfig functionDimensions
def functionsDeficientOption (x : Input (RationalFn Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsDeficientOption n => n ^ 3 with prep := functionsDeficientInput
  where dimConfig functionDimensions
def functionsDeficientInverse (x : Input (RationalFn Rat)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsDeficientInverse n => n ^ 3 with prep := functionsDeficientInput
  where dimConfig functionDimensions

def functionsHalfInput (n : Nat) : Input (RationalFn Rat) := functions n 2
def functionsHalfSolve (x : Input (RationalFn Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsHalfSolve n => n ^ 3 with prep := functionsHalfInput
  where dimConfig functionDimensions
def functionsHalfOption (x : Input (RationalFn Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsHalfOption n => n ^ 3 with prep := functionsHalfInput
  where dimConfig functionDimensions
def functionsHalfInverse (x : Input (RationalFn Rat)) : UInt64 := inverse x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsHalfInverse n => n ^ 3 with prep := functionsHalfInput
  where dimConfig functionDimensions

def functionsDeficientErrorInput (n : Nat) : Input (RationalFn Rat) := functions n 3
def functionsDeficientErrorSolve (x : Input (RationalFn Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsDeficientErrorSolve n => n ^ 3 with prep := functionsDeficientErrorInput
  where dimConfig functionDimensions
def functionsDeficientErrorOption (x : Input (RationalFn Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsDeficientErrorOption n => n ^ 3 with prep := functionsDeficientErrorInput
  where dimConfig functionDimensions

def functionsHalfErrorInput (n : Nat) : Input (RationalFn Rat) := functions n 4
def functionsHalfErrorSolve (x : Input (RationalFn Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsHalfErrorSolve n => n ^ 3 with prep := functionsHalfErrorInput
  where dimConfig functionDimensions
def functionsHalfErrorOption (x : Input (RationalFn Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsHalfErrorOption n => n ^ 3 with prep := functionsHalfErrorInput
  where dimConfig functionDimensions

def functionsTallInput (n : Nat) : Input (RationalFn Rat) := functions n 5
def functionsTallSolve (x : Input (RationalFn Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsTallSolve n => n ^ 3 with prep := functionsTallInput
  where dimConfig functionDimensions
def functionsTallOption (x : Input (RationalFn Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsTallOption n => n ^ 3 with prep := functionsTallInput
  where dimConfig functionDimensions

def functionsWideInput (n : Nat) : Input (RationalFn Rat) := functions n 6
def functionsWideSolve (x : Input (RationalFn Rat)) : UInt64 := solve x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsWideSolve n => n ^ 3 with prep := functionsWideInput
  where dimConfig functionDimensions
def functionsWideOption (x : Input (RationalFn Rat)) : UInt64 := solveOption x
-- Cubic: rank-proportional dense elimination; RHS and basis work are at most quadratic.
setup_benchmark functionsWideOption n => n ^ 3 with prep := functionsWideInput
  where dimConfig functionDimensions

def height8FullInput (n : Nat) : Input (Rat) := rational (max 8 n) 8 0
def height8FullSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8FullSolve n => n ^ 2 with prep := height8FullInput
  where dimConfig heights
def height8FullOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8FullOption n => n ^ 2 with prep := height8FullInput
  where dimConfig heights
def height8FullInverse (x : Input (Rat)) : UInt64 := inverse x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8FullInverse n => n ^ 2 with prep := height8FullInput
  where dimConfig heights

def height8DeficientInput (n : Nat) : Input (Rat) := rational (max 8 n) 8 1
def height8DeficientSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8DeficientSolve n => n ^ 2 with prep := height8DeficientInput
  where dimConfig heights
def height8DeficientOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8DeficientOption n => n ^ 2 with prep := height8DeficientInput
  where dimConfig heights
def height8DeficientInverse (x : Input (Rat)) : UInt64 := inverse x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8DeficientInverse n => n ^ 2 with prep := height8DeficientInput
  where dimConfig heights

def height8HalfInput (n : Nat) : Input (Rat) := rational (max 8 n) 8 2
def height8HalfSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8HalfSolve n => n ^ 2 with prep := height8HalfInput
  where dimConfig heights
def height8HalfOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8HalfOption n => n ^ 2 with prep := height8HalfInput
  where dimConfig heights
def height8HalfInverse (x : Input (Rat)) : UInt64 := inverse x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8HalfInverse n => n ^ 2 with prep := height8HalfInput
  where dimConfig heights

def height8DeficientErrorInput (n : Nat) : Input (Rat) := rational (max 8 n) 8 3
def height8DeficientErrorSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8DeficientErrorSolve n => n ^ 2 with prep := height8DeficientErrorInput
  where dimConfig heights
def height8DeficientErrorOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8DeficientErrorOption n => n ^ 2 with prep := height8DeficientErrorInput
  where dimConfig heights

def height8HalfErrorInput (n : Nat) : Input (Rat) := rational (max 8 n) 8 4
def height8HalfErrorSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8HalfErrorSolve n => n ^ 2 with prep := height8HalfErrorInput
  where dimConfig heights
def height8HalfErrorOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8HalfErrorOption n => n ^ 2 with prep := height8HalfErrorInput
  where dimConfig heights

def height8TallInput (n : Nat) : Input (Rat) := rational (max 8 n) 8 5
def height8TallSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8TallSolve n => n ^ 2 with prep := height8TallInput
  where dimConfig heights
def height8TallOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8TallOption n => n ^ 2 with prep := height8TallInput
  where dimConfig heights

def height8WideInput (n : Nat) : Input (Rat) := rational (max 8 n) 8 6
def height8WideSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8WideSolve n => n ^ 2 with prep := height8WideInput
  where dimConfig heights
def height8WideOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height8WideOption n => n ^ 2 with prep := height8WideInput
  where dimConfig heights

def height16FullInput (n : Nat) : Input (Rat) := rational (max 8 n) 16 0
def height16FullSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16FullSolve n => n ^ 2 with prep := height16FullInput
  where dimConfig heights
def height16FullOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16FullOption n => n ^ 2 with prep := height16FullInput
  where dimConfig heights
def height16FullInverse (x : Input (Rat)) : UInt64 := inverse x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16FullInverse n => n ^ 2 with prep := height16FullInput
  where dimConfig heights

def height16DeficientInput (n : Nat) : Input (Rat) := rational (max 8 n) 16 1
def height16DeficientSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16DeficientSolve n => n ^ 2 with prep := height16DeficientInput
  where dimConfig heights
def height16DeficientOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16DeficientOption n => n ^ 2 with prep := height16DeficientInput
  where dimConfig heights
def height16DeficientInverse (x : Input (Rat)) : UInt64 := inverse x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16DeficientInverse n => n ^ 2 with prep := height16DeficientInput
  where dimConfig heights

def height16HalfInput (n : Nat) : Input (Rat) := rational (max 8 n) 16 2
def height16HalfSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16HalfSolve n => n ^ 2 with prep := height16HalfInput
  where dimConfig heights
def height16HalfOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16HalfOption n => n ^ 2 with prep := height16HalfInput
  where dimConfig heights
def height16HalfInverse (x : Input (Rat)) : UInt64 := inverse x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16HalfInverse n => n ^ 2 with prep := height16HalfInput
  where dimConfig heights

def height16DeficientErrorInput (n : Nat) : Input (Rat) := rational (max 8 n) 16 3
def height16DeficientErrorSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16DeficientErrorSolve n => n ^ 2 with prep := height16DeficientErrorInput
  where dimConfig heights
def height16DeficientErrorOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16DeficientErrorOption n => n ^ 2 with prep := height16DeficientErrorInput
  where dimConfig heights

def height16HalfErrorInput (n : Nat) : Input (Rat) := rational (max 8 n) 16 4
def height16HalfErrorSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16HalfErrorSolve n => n ^ 2 with prep := height16HalfErrorInput
  where dimConfig heights
def height16HalfErrorOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16HalfErrorOption n => n ^ 2 with prep := height16HalfErrorInput
  where dimConfig heights

def height16TallInput (n : Nat) : Input (Rat) := rational (max 8 n) 16 5
def height16TallSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16TallSolve n => n ^ 2 with prep := height16TallInput
  where dimConfig heights
def height16TallOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16TallOption n => n ^ 2 with prep := height16TallInput
  where dimConfig heights

def height16WideInput (n : Nat) : Input (Rat) := rational (max 8 n) 16 6
def height16WideSolve (x : Input (Rat)) : UInt64 := solve x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16WideSolve n => n ^ 2 with prep := height16WideInput
  where dimConfig heights
def height16WideOption (x : Input (Rat)) : UInt64 := solveOption x
-- Upper bound: fixed dimension gives O(h)-bit intermediates; schoolbook arithmetic
-- and Lehmer GCD cost O(h²). See gmplib.org/manual/Lehmer_0027s-Algorithm.
setup_benchmark height16WideOption n => n ^ 2 with prep := height16WideInput
  where dimConfig heights

private def ratJson (q : Rat) : Lean.Json :=
  toJson #[toJson q.num, toJson q.den]
private def matrixJson (A : Matrix Rat n m) : Lean.Json :=
  let data := A.data.toArray
  let width := data.size / n
  toJson ((List.range n).map fun i =>
    toJson ((data.extract (i * width) ((i + 1) * width)).map ratJson))

private def leanAt (op : String) (input : Input Rat) : Unit → IO String :=
  fun _ => do
    if op == "field_inverse" then
      if h : input.m = input.n then
        match Matrix.inverse? (h ▸ input.A) with
        | none => throw (IO.userError "unexpected inverse failure")
        | some B => return (matrixJson B).compress
      else throw (IO.userError "not square")
    else
      match Matrix.solve input.A input.b with
      | .error _ => throw (IO.userError "unexpected solve failure")
      | .ok (x, N) => return (toJson #[toJson (x.toArray.map ratJson), matrixJson N]).compress

private def flintFields (input : Input Rat) : Array (String × Lean.Json) :=
  #[("n", toJson input.n), ("rows", matrixJson input.A),
    ("rhs", toJson (input.b.toArray.map ratJson))]

private def flintAt (op : String) (fields : Array (String × Lean.Json)) : Unit → IO String :=
  fun _ => do
    return (← Hex.BenchOracle.Flint.runOp "fmpq_mat" op fields).compress

private def comparisonConfig (expected : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 4, maxSecondsPerCall := 30.0, minTotalSeconds := 0.2,
    warmupFirstIter := true, expectedHash := some expected }

-- Closed constants are prepared once; the timed functions receive only cached inputs.
private def input8 := rational 32 8 0
private def fields8 := flintFields input8
private def input16 := rational 32 16 0
private def fields16 := flintFields input16
private def input32 := rational 32 32 0
private def fields32 := flintFields input32
def leanInverse8 := leanAt "field_inverse" input8
def flintInverse8 := flintAt "field_inverse" fields8
def leanSolve8 := leanAt "field_solve" input8
def flintSolve8 := flintAt "field_solve" fields8
def leanInverse16 := leanAt "field_inverse" input16
def flintInverse16 := flintAt "field_inverse" fields16
def leanSolve16 := leanAt "field_solve" input16
def flintSolve16 := flintAt "field_solve" fields16
def leanInverse32 := leanAt "field_inverse" input32
def flintInverse32 := flintAt "field_inverse" fields32
def leanSolve32 := leanAt "field_solve" input32
def flintSolve32 := flintAt "field_solve" fields32

setup_fixed_benchmark leanInverse8 where comparisonConfig 0x386bde7013009693
setup_fixed_benchmark flintInverse8 where comparisonConfig 0x386bde7013009693
setup_fixed_benchmark leanSolve8 where comparisonConfig 0x9a2a4e0d29ac0f9
setup_fixed_benchmark flintSolve8 where comparisonConfig 0x9a2a4e0d29ac0f9
setup_fixed_benchmark leanInverse16 where comparisonConfig 0xc0e229f2fbba2a35
setup_fixed_benchmark flintInverse16 where comparisonConfig 0xc0e229f2fbba2a35
setup_fixed_benchmark leanSolve16 where comparisonConfig 0x6da2044201524393
setup_fixed_benchmark flintSolve16 where comparisonConfig 0x6da2044201524393
setup_fixed_benchmark leanInverse32 where comparisonConfig 0x18ded232abb746bd
setup_fixed_benchmark flintInverse32 where comparisonConfig 0x18ded232abb746bd
setup_fixed_benchmark leanSolve32 where comparisonConfig 0x2de9fc4d9d0ecd4
setup_fixed_benchmark flintSolve32 where comparisonConfig 0x2de9fc4d9d0ecd4

private def bits (n : Nat) : Nat := if n == 0 then 0 else n.log2 + 1
private def ratHeights (q : Rat) : Nat × Nat := (bits q.num.natAbs, bits q.den)
private def fnHeights (f : RationalFn Rat) : Nat × Nat :=
  (f.num.toArray ++ f.den.toArray).foldl (fun (a, b) q =>
    (max a (ratHeights q).1, max b (ratHeights q).2)) (0, 0)

private def metadata (carrier axis : String) (param height family : Nat)
    (x : Input F) (heights : F → Nat × Nat) (degree : F → Nat) : Lean.Json :=
  let actual := x.A.data.toArray.foldl (fun (a, b) q =>
    (max a (heights q).1, max b (heights q).2)) (0, 0)
  let rhs := x.b.toArray.foldl (fun (a, b) q =>
    (max a (heights q).1, max b (heights q).2)) (0, 0)
  Lean.Json.mkObj [("carrier", toJson carrier), ("axis", toJson axis),
    ("parameter", toJson param), ("requested_height", toJson height),
    ("family", toJson family), ("n", toJson x.n), ("m", toJson x.m),
    ("rank", toJson x.rank), ("seed", toJson (10222 : Nat)),
    ("input_hash", toJson (hash x).toNat), ("numerator_bits", toJson actual.1),
    ("denominator_bits", toJson actual.2), ("rhs_numerator_bits", toJson rhs.1),
    ("rhs_denominator_bits", toJson rhs.2),
    ("degree", toJson (x.A.data.toArray.foldl (fun d q => max d (degree q)) 0))]

/-- Reproduce the input hashes, checked ranks, and actual coefficient heights
for every scientific rung without collecting timings. -/
def emitMetadata : IO Unit := do
  for h in #[8, 32, 128] do
    for n in dimensions do
      for f in [:7] do
        IO.println (metadata "Rat" "dimension" n h f (rational h n f) ratHeights (fun _ => 0)).compress
  for n in #[8, 16] do
    for h in heights do
      for f in [:7] do
        IO.println (metadata "Rat" "height" h h f (rational h n f) ratHeights (fun _ => 0)).compress
  for n in dimensions do
    for f in [:7] do
      IO.println (metadata "ZMod64/101" "dimension" n 0 f (modular n f)
        (fun q => (bits q.toNat, 1)) (fun _ => 0)).compress
  for n in functionDimensions do
    for f in [:7] do
      IO.println (metadata "RationalFn Rat" "dimension" n 8 f (functions n f) fnHeights
        (fun q => max (q.num.toArray.size - 1) (q.den.toArray.size - 1))).compress

end Field

end Hex.RowReduceBench

def main (args : List String) : IO UInt32 := do
  if args == ["field-inputs"] then
    Hex.RowReduceBench.Field.emitMetadata
    return 0
  LeanBench.Cli.dispatch args
