/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSmith
import Hex.BenchOracle.Flint
import Hex.BenchOracle.Pari
import Lean.Data.Json
import LeanBench

/-! Mathlib-free Smith benchmarks over the input families fixed by the SPEC,
including informational FLINT/PARI comparisons and untimed entry-growth
instrumentation. -/

namespace Hex.SmithBench

structure Input where
  rows : Nat
  cols : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

private def noise (salt n i j : Nat) : Int :=
  Int.ofNat (((i + 3) * 29 + (j + 5) * 43 + n * 17 + salt) % 31) - 15

/-- Uniform-looking dense, diagonally shifted square input. -/
def dense (n : Nat) : Input :=
  { rows := n, cols := n
    entries := (Array.range (n * n)).map fun k =>
      let i := k / n
      let j := k % n
      noise 7 n i j + if i = j then Int.ofNat (32 * n + 1) else 0 }

/-- A known chain conjugated by unit lower/upper triangular matrices. -/
def chainConjugate (n : Nat) : Input :=
  { rows := n, cols := n
    entries := (Array.range (n * n)).map fun k =>
      let i := k / n
      let j := k % n
      (List.finRange n).foldl (fun acc t =>
        let u : Int := if t.val = i then 1 else if t.val < i then noise 19 n i t.val else 0
        let d : Int := Int.ofNat (2 ^ (t.val + 1))
        let v : Int := if t.val = j then 1 else if j < t.val then noise 23 n t.val j else 0
        acc + u * d * v) 0 }

/-- Sparse relation matrices resembling direct presentations with a handful
of mixed generators. -/
def presentation (n : Nat) : Input :=
  { rows := n, cols := n
    entries := (Array.range (n * n)).map fun k =>
      let i := k / n
      let j := k % n
      if i = j then Int.ofNat (2 * (i + 1))
      else if j + 1 = i then -1
      else if i + 2 = j then 1
      else 0 }

private def matrix (input : Input) : Matrix Int input.rows input.cols :=
  Matrix.ofFn fun i j => input.entries.getD (i.val * input.cols + j.val) 0

private def checksum (M : Matrix Int n m) : Int :=
  M.data.foldl (fun acc x => acc * 65537 + x) 0

private def dataChecksum (D : Matrix.SmithData n m) : Int :=
  checksum D.left + 3 * checksum D.leftInv + 5 * checksum D.right +
    7 * checksum D.rightInv + D.diag.toList.foldl (fun acc x => 11 * acc + x) 0

private def diagonal (n : Nat) : Vector Int n :=
  Vector.ofFn fun i => if i.val % 5 = 0 then 0
    else if i.val % 3 = 0 then -Int.ofNat (2 * (i.val + 1))
    else Int.ofNat (3 * (i.val + 1))

private def bitLength (z : Int) : Nat :=
  let n := z.natAbs
  if n = 0 then 0 else n.log2 + 1

private def matrixBits (M : Matrix Int n m) : Nat :=
  M.data.foldl (fun peak z => max peak (bitLength z)) 0

/-- State for the deliberately untimed entry-growth runner. -/
private structure GrowthState (n m : Nat) where
  result : Matrix.Smith.Result Unit n m
  peak : Nat

private def observe (s : Matrix.Smith.Result Unit n m) (peak : Nat) :
    GrowthState n m :=
  ⟨s, max peak (matrixBits s.matrix)⟩

private def growthRepair (s : GrowthState n m) (pivotRow row : Fin n)
    (pivotCol col : Fin m) : GrowthState n m :=
  let matrix := Matrix.rowAdd s.result.matrix row pivotRow 1
  let rowAdded : Matrix.Smith.Result Unit n m := { s.result with matrix := matrix }
  let first := observe rowAdded s.peak
  let p := matrix[(pivotRow, pivotCol)]
  let b := matrix[(pivotRow, col)]
  let (a, b', c, d) := Matrix.Hermite.gcdCoeffs p b
  observe { rowAdded with
    matrix := Matrix.Hermite.combineCols matrix pivotCol col a b' c d } first.peak

private def growthReduceFuel (pivotRow : Fin n) (pivotCol : Fin m) :
    Nat → GrowthState n m → GrowthState n m
  | 0, s => s
  | fuel + 1, s =>
      let p := s.result.matrix[(pivotRow, pivotCol)]
      if p = 0 then s
      else
        match Matrix.Smith.findColumn? s.result.matrix pivotRow pivotCol with
        | some row =>
            let next := observe
              (Matrix.Smith.clearColumn (Matrix.Smith.formAccumulator n m)
                s.result pivotRow row pivotCol) s.peak
            growthReduceFuel pivotRow pivotCol fuel next
        | none =>
            match Matrix.Smith.findRow? s.result.matrix pivotRow pivotCol with
            | some col =>
                let next := observe
                  (Matrix.Smith.clearRow (Matrix.Smith.formAccumulator n m)
                    s.result pivotRow pivotCol col) s.peak
                growthReduceFuel pivotRow pivotCol fuel next
            | none =>
                if p < 0 then
                  let normalized := observe { s.result with
                    matrix := Matrix.rowScale s.result.matrix pivotRow (-1) } s.peak
                  let p' := normalized.result.matrix[(pivotRow, pivotCol)]
                  match Matrix.Smith.findBad? normalized.result.matrix
                      pivotRow pivotCol p' with
                  | none => normalized
                  | some q => growthReduceFuel pivotRow pivotCol fuel
                      (growthRepair normalized pivotRow q.1 pivotCol q.2)
                else
                  match Matrix.Smith.findBad? s.result.matrix pivotRow pivotCol p with
                  | none => s
                  | some q => growthReduceFuel pivotRow pivotCol fuel
                      (growthRepair s pivotRow q.1 pivotCol q.2)

private def growthReduce (s : GrowthState n m) (pivotRow : Fin n)
    (pivotCol : Fin m) : GrowthState n m :=
  let p := s.result.matrix[(pivotRow, pivotCol)]
  growthReduceFuel pivotRow pivotCol
    ((p.natAbs + 1) * (n + m + 1) + 1) s

private def growthRunFuel : Nat → GrowthState n m → GrowthState n m
  | 0, s => s
  | fuel + 1, s =>
      let k := s.result.diag.length
      if hn : k < n then
        if hm : k < m then
          match Matrix.Smith.findPivot? s.result.matrix k with
          | none => s
          | some q =>
              let pivotRow : Fin n := ⟨k, hn⟩
              let pivotCol : Fin m := ⟨k, hm⟩
              let rows := observe
                (Matrix.Smith.swapRows (Matrix.Smith.formAccumulator n m)
                  s.result pivotRow q.1) s.peak
              let cols := observe
                (Matrix.Smith.swapCols (Matrix.Smith.formAccumulator n m)
                  rows.result pivotCol q.2) rows.peak
              let reduced := growthReduce cols pivotRow pivotCol
              let p := reduced.result.matrix[(pivotRow, pivotCol)]
              if p = 0 then reduced
              else growthRunFuel fuel { reduced with result :=
                { reduced.result with diag := reduced.result.diag ++ [p] } }
        else s
      else s

/-- Scan the working matrix after every row or column update and return the
peak intermediate entry bit-size. Timed benchmarks use only the ordinary
uninstrumented API. -/
def peakBits (input : Input) : Nat :=
  let A := matrix input
  let initial : GrowthState input.rows input.cols :=
    { result := { matrix := A, diag := [], accumulator := () }
      peak := matrixBits A }
  (growthRunFuel (Nat.min input.rows input.cols) initial).peak

private def emitGrowth (family : String) (n : Nat) (input : Input) : IO Unit := do
  let A := matrix input
  let form := Matrix.snf A
  let peak := peakBits input
  IO.println s!"{family},{n},{peak},{matrixBits form}"

/-- Emit untimed `family,n,peak_bits,output_bits` growth diagnostics. -/
def growthReport : IO UInt32 := do
  IO.println "family,n,peak_bits,output_bits"
  for n in #[2, 4, 8, 12, 16] do
    emitGrowth "random-dense-smith" n (dense n)
    emitGrowth "chain-conjugate" n (chainConjugate n)
  for n in #[2, 4, 8, 16, 24] do
    emitGrowth "presentation-smith" n (presentation n)
  return 0

def runDense (input : Input) : Int := checksum (Matrix.snf (matrix input))
def runChain (input : Input) : Int := checksum (Matrix.snf (matrix input))
def runPresentation (input : Input) : Int := checksum (Matrix.snf (matrix input))
def runData (input : Input) : Int := dataChecksum (Matrix.snfData (matrix input))
def runDiagonal (n : Nat) : Int := checksum (Matrix.snfDiagonal (diagonal n))
def runDiagonalGeneral (n : Nat) : Int :=
  checksum (Matrix.snf (Matrix.diagMatrix (diagonal n) n n))
def runDiagonalData (n : Nat) : Int := dataChecksum (Matrix.snfDiagonalData (diagonal n))

private def inputRowsJson (input : Input) : Lean.Json :=
  Lean.Json.arr (Array.ofFn fun i : Fin input.rows =>
    Hex.BenchOracle.Flint.intsToJson
      (List.ofFn fun j : Fin input.cols =>
        input.entries.getD (i.val * input.cols + j.val) 0))

private def runHexAt (n : Nat) (_ : Unit) : IO (List Int) :=
  return (Matrix.invariantFactors (matrix (dense n))).toList

private def runFlintAt (n : Nat) (_ : Unit) : IO (List Int) := do
  let input := dense n
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mat" "snf"
    #[("rows", inputRowsJson input)]
  Hex.BenchOracle.Flint.jsonToInts result

private def runPariAt (n : Nat) (_ : Unit) : IO (List Int) := do
  let input := dense n
  let result ← Hex.BenchOracle.Pari.runOp "fmpz_mat" "snf"
    #[("rows", inputRowsJson input)]
  Hex.BenchOracle.Flint.jsonToInts result

def runHex6 : Unit → IO (List Int) := runHexAt 6
def runFlint6 : Unit → IO (List Int) := runFlintAt 6
def runPari6 : Unit → IO (List Int) := runPariAt 6
def runHex10 : Unit → IO (List Int) := runHexAt 10
def runFlint10 : Unit → IO (List Int) := runFlintAt 10
def runPari10 : Unit → IO (List Int) := runPariAt 10
def runHex14 : Unit → IO (List Int) := runHexAt 14
def runFlint14 : Unit → IO (List Int) := runFlintAt 14
def runPari14 : Unit → IO (List Int) := runPariAt 14

/- Cost model: for square input, each of `n` pivots scans the trailing block
and performs linear-many row/column updates, giving the SPEC's cubic
matrix-update model when the pivot-repeat factor is held fixed. -/
setup_benchmark runDense n => n ^ 3 with prep := dense where {
  paramFloor := 2, paramCeiling := 16, paramSchedule := .custom #[2, 4, 8, 12, 16]
  maxSecondsPerCall := 10.0
}

/- Cost model: conjugation changes the entries but not the classical pivot
schedule, so the same cubic matrix-update bound applies. -/
setup_benchmark runChain n => n ^ 3 with prep := chainConjugate where {
  paramFloor := 2, paramCeiling := 16, paramSchedule := .custom #[2, 4, 8, 12, 16]
  maxSecondsPerCall := 10.0
}

/- Cost model: the v1 implementation intentionally runs sparse presentations
through the dense classical loop, hence the same cubic matrix-update model. -/
setup_benchmark runPresentation n => n ^ 3 with prep := presentation where {
  paramFloor := 2, paramCeiling := 24, paramSchedule := .custom #[2, 4, 8, 16, 24]
  maxSecondsPerCall := 10.0
}

/- Cost model: accumulating four dense transforms adds linear work to each of
quadratically many elimination updates, retaining the cubic model. -/
setup_benchmark runData n => n ^ 3 with prep := dense where {
  paramFloor := 2, paramCeiling := 12, paramSchedule := .custom #[2, 4, 8, 12]
  maxSecondsPerCall := 10.0
}

/- Cost model: the fixed network performs `n` full adjacent passes, hence a
quadratic number of gcd/lcm pair steps and no dense elimination. -/
setup_benchmark runDiagonal n => n ^ 2 where {
  paramFloor := 4, paramCeiling := 32, paramSchedule := .custom #[4, 8, 16, 24, 32]
  maxSecondsPerCall := 10.0
}

/- Cost model: routing the same diagonal input through the general dense pivot
loop retains its conservative cubic matrix-update model. -/
setup_benchmark runDiagonalGeneral n => n ^ 3 where {
  paramFloor := 4, paramCeiling := 32, paramSchedule := .custom #[4, 8, 16, 24, 32]
  maxSecondsPerCall := 10.0
}

/- Cost model: the quadratic pair network updates dense transform matrices at
each step, producing cubic scalar-entry work. -/
setup_benchmark runDiagonalData n => n ^ 3 where {
  paramFloor := 4, paramCeiling := 24, paramSchedule := .custom #[4, 8, 16, 24]
  maxSecondsPerCall := 10.0
}

private def hexComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := 10.0

private def externalComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := 10.0
  warmupFirstIter := true

setup_fixed_benchmark runHex6 where hexComparisonConfig
setup_fixed_benchmark runFlint6 where externalComparisonConfig
setup_fixed_benchmark runPari6 where externalComparisonConfig
setup_fixed_benchmark runHex10 where hexComparisonConfig
setup_fixed_benchmark runFlint10 where externalComparisonConfig
setup_fixed_benchmark runPari10 where externalComparisonConfig
setup_fixed_benchmark runHex14 where hexComparisonConfig
setup_fixed_benchmark runFlint14 where externalComparisonConfig
setup_fixed_benchmark runPari14 where externalComparisonConfig

end Hex.SmithBench

def main (args : List String) : IO UInt32 :=
  match args with
  | ["growth"] => Hex.SmithBench.growthReport
  | _ => LeanBench.Cli.dispatch args
