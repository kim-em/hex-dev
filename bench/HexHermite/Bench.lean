/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexHermite
import Hex.BenchOracle.Flint
import Hex.BenchOracle.Pari
import LeanBench

/-! Mathlib-free HNF benchmarks over the four input families fixed by the SPEC. -/

namespace Hex.HermiteBench

structure Input where
  rows : Nat
  cols : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

private def entry (salt n i j : Nat) : Int :=
  let x := (i + 1) * 2654435761 + (j + 3) * 2246822519 +
    (i + salt + 1) * (j + n + 3) * 3266489917
  Int.ofNat ((x + x / 97 + x / 1000003) % 21) - 10

def dense (n : Nat) : Input :=
  { rows := n, cols := n
    entries := (Array.range (n * n)).map fun k =>
      let i := k / n
      let j := k % n
      entry 5 n i j }

def deficient (n : Nat) : Input :=
  let rank := n / 2
  { rows := n, cols := n
    entries := (Array.range (n * n)).map fun k =>
      let i := k / n
      let j := k % n
      if i < rank then entry 17 n i j
      else if rank = 0 then 0 else entry 17 n (i % rank) j * Int.ofNat (i + 1) }

def tall (n : Nat) : Input :=
  let rows := 4 * n
  { rows := rows, cols := n
    entries := (Array.range (rows * n)).map fun k =>
      let i := k / n
      let j := k % n
      let source := if n = 0 then 0 else i % n
      let value : Int := if source = j then 2 else 1
      if i < n ∨ i % 2 = 0 then value else -value }

def conjugate (n : Nat) : Input :=
  { rows := n, cols := n
    entries := (Array.range (n * n)).map fun k =>
      let i := k / n
      let j := k % n
      if j = i then Int.ofNat (i + 2)
      else if j < i then Int.ofNat ((i - j + 1) * (j + 2))
      else 0 }

private def matrix (input : Input) : Matrix Int input.rows input.cols :=
  Matrix.ofFn fun i j => input.entries.getD (i.val * input.cols + j.val) 0

private def checksum (M : Matrix Int n m) : Int :=
  M.data.foldl (fun acc x => acc * 65537 + x) 0

private def bitLength (z : Int) : Nat :=
  let n := z.natAbs
  if n = 0 then 0 else n.log2 + 1

private def matrixBits (M : Matrix Int n m) : Nat :=
  M.data.foldl (fun largest z => max largest (bitLength z)) 0

/-- Diagnostic state for the deliberately untimed entry-growth runner. -/
private structure GrowthState (n m : Nat) where
  result : Matrix.Hermite.Result Unit n m
  peak : Nat

private def observe (s : Matrix.Hermite.Result Unit n m) (peak : Nat) :
    GrowthState n m :=
  ⟨s, max peak (matrixBits s.matrix)⟩

private def growthClear (s : GrowthState n m) (col : Fin m)
    (pivot found : Fin n) : GrowthState n m :=
  let ops := Matrix.Hermite.formAccumulator n
  let s := observe (Matrix.Hermite.swapStep ops s.result pivot found) s.peak
  let s := (List.finRange n).foldl (fun s k =>
    if pivot.val < k.val then
      observe (Matrix.Hermite.gcdStep ops col pivot k s.result) s.peak
    else s) s
  let s := observe (Matrix.Hermite.signStep ops col pivot s.result) s.peak
  (List.finRange n).foldl (fun s k =>
    if k.val < pivot.val then
      observe (Matrix.Hermite.reduceStep ops col pivot k s.result) s.peak
    else s) s

private def growthColumn (s : GrowthState n m) (col : Fin m) : GrowthState n m :=
  if hr : s.result.pivots.length < n then
    let pivot : Fin n := ⟨s.result.pivots.length, hr⟩
    match Matrix.Hermite.findPivot? s.result.matrix col s.result.pivots.length with
    | none => s
    | some found =>
        let next := growthClear s col pivot found
        { next with result := { next.result with pivots := next.result.pivots ++ [col] } }
  else s

/-- Scan the working matrix after every elementary update and return the peak
coefficient bit-size. This runner is intentionally separate from timed
benchmarks so instrumentation does not perturb ordinary timings. -/
def peakBits (input : Input) : Nat :=
  let A := matrix input
  let initial : GrowthState input.rows input.cols :=
    { result :=
        { matrix := A, pivots := []
          accumulator := (Matrix.Hermite.formAccumulator input.rows).init }
      peak := matrixBits A }
  ((List.finRange input.cols).foldl growthColumn initial).peak

/-- Peak-versus-output growth data for the predeclared badly-conditioned
family. -/
def conjugateGrowth (n : Nat) : Nat × Nat :=
  let input := conjugate n
  (peakBits input, matrixBits (Matrix.hnf (matrix input)))

def runDense (input : Input) : Int := checksum (Matrix.hnf (matrix input))
def runDeficient (input : Input) : Int := checksum (Matrix.hnf (matrix input))
def runTall (input : Input) : Int := checksum (Matrix.hnf (matrix input))
def runConjugate (input : Input) : Int := checksum (Matrix.hnf (matrix input))

private def vectorChecksum (v : Vector Int n) : Int :=
  v.foldl (fun acc x => acc * 65537 + x) 0

private def fixedMatrix : Matrix Int 8 8 := matrix (dense 8)

private def fixedCertificate : Matrix.HermiteData 8 8 :=
  Matrix.hnfWithInv fixedMatrix

private def live (value : α) : IO α := do
  let ref ← IO.mkRef value
  ref.get

def runIsHNFForm (_ : Unit) : IO Bool := do
  let certificate ← live fixedCertificate
  let D := certificate.rowData
  return Matrix.isHNFForm D.echelon D.rank D.pivotCols

def runRank (_ : Unit) : IO Nat := do
  let A ← live fixedMatrix
  return Matrix.hnfRank A

def runBasis (_ : Unit) : IO Int := do
  let A ← live fixedMatrix
  return checksum (Matrix.hnfBasis A)

def runData (_ : Unit) : IO Int := do
  let A ← live fixedMatrix
  let D := Matrix.hnfData A
  return checksum D.echelon + checksum D.transform + Int.ofNat D.rank

def runWithInv (_ : Unit) : IO Int := do
  let A ← live fixedMatrix
  let D := Matrix.hnfWithInv A
  return checksum D.rowData.echelon + checksum D.rowData.transform + checksum D.inverse

def runCoeffs (_ : Unit) : IO Int := do
  let A ← live fixedMatrix
  return match Matrix.latticeCoeffs A (Matrix.row A 0) with
    | some c => vectorChecksum c
    | none => -1

def runContains (_ : Unit) : IO Bool := do
  let A ← live fixedMatrix
  return Matrix.latticeContains A (Matrix.row A 0)

def runKernelBasis (_ : Unit) : IO Int := do
  let A ← live fixedMatrix
  return checksum (Matrix.kernelBasis A)

def runPivots (_ : Unit) : IO Nat := do
  let A ← live fixedMatrix
  return (Matrix.pivots A).foldl (fun acc x => acc * 65537 + x) 0

def runIndex (_ : Unit) : IO Nat := do
  let A ← live fixedMatrix
  return Matrix.latticeIndex A

def runCert (_ : Unit) : IO Bool := do
  let A ← live fixedMatrix
  let certificate ← live fixedCertificate
  let D := certificate.rowData
  return Matrix.hnfCert A D.echelon D.transform certificate.inverse D.rank D.pivotCols

private def rowsJson (input : Input) : Lean.Json :=
  Lean.Json.arr (Array.ofFn fun i : Fin input.rows =>
    Hex.BenchOracle.Flint.intsToJson
      (List.ofFn fun j : Fin input.cols => (matrix input)[(i, j)]))

private def jsonMatrixChecksum (json : Lean.Json) : IO Int := do
  let rows ← match json.getArr? with
    | .ok value => pure value
    | .error error => throw <| IO.userError s!"expected matrix rows: {error}"
  let mut acc : Int := 0
  for rowJson in rows do
    let row ← match rowJson.getArr? with
      | .ok value => pure value
      | .error error => throw <| IO.userError s!"expected matrix row: {error}"
    for valueJson in row do
      let value ← match valueJson.getInt? with
        | .ok value => pure value
        | .error error => throw <| IO.userError s!"expected integer entry: {error}"
      acc := acc * 65537 + value
  return acc

private def runHexAt (input : Input) (_ : Unit) : IO Int := do
  let ref ← IO.mkRef input
  let live ← ref.get
  return checksum (Matrix.hnf (matrix live))

private def runFlintAt (input : Input) (_ : Unit) : IO Int := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mat" "hnf"
    #[("rows", rowsJson input)]
  jsonMatrixChecksum result

private def runPariAt (input : Input) (_ : Unit) : IO Int := do
  let result ← Hex.BenchOracle.Pari.runOp "fmpz_mat" "hnf"
    #[("rows", rowsJson input)]
  jsonMatrixChecksum result

def runHexDense16 : Unit → IO Int := runHexAt (dense 16)
def runFlintDense16 : Unit → IO Int := runFlintAt (dense 16)
def runPariDense16 : Unit → IO Int := runPariAt (dense 16)
def runHexDense24 : Unit → IO Int := runHexAt (dense 24)
def runFlintDense24 : Unit → IO Int := runFlintAt (dense 24)
def runPariDense24 : Unit → IO Int := runPariAt (dense 24)
def runHexDense32 : Unit → IO Int := runHexAt (dense 32)
def runFlintDense32 : Unit → IO Int := runFlintAt (dense 32)
def runPariDense32 : Unit → IO Int := runPariAt (dense 32)
def runHexDense40 : Unit → IO Int := runHexAt (dense 40)
def runFlintDense40 : Unit → IO Int := runFlintAt (dense 40)
def runPariDense40 : Unit → IO Int := runPariAt (dense 40)
def runHexDeficient16 : Unit → IO Int := runHexAt (deficient 16)
def runFlintDeficient16 : Unit → IO Int := runFlintAt (deficient 16)
def runPariDeficient16 : Unit → IO Int := runPariAt (deficient 16)
def runHexDeficient24 : Unit → IO Int := runHexAt (deficient 24)
def runFlintDeficient24 : Unit → IO Int := runFlintAt (deficient 24)
def runPariDeficient24 : Unit → IO Int := runPariAt (deficient 24)
def runHexDeficient32 : Unit → IO Int := runHexAt (deficient 32)
def runFlintDeficient32 : Unit → IO Int := runFlintAt (deficient 32)
def runPariDeficient32 : Unit → IO Int := runPariAt (deficient 32)
def runHexDeficient40 : Unit → IO Int := runHexAt (deficient 40)
def runFlintDeficient40 : Unit → IO Int := runFlintAt (deficient 40)
def runPariDeficient40 : Unit → IO Int := runPariAt (deficient 40)
def runHexTall16 : Unit → IO Int := runHexAt (tall 16)
def runFlintTall16 : Unit → IO Int := runFlintAt (tall 16)
def runPariTall16 : Unit → IO Int := runPariAt (tall 16)
def runHexTall24 : Unit → IO Int := runHexAt (tall 24)
def runFlintTall24 : Unit → IO Int := runFlintAt (tall 24)
def runPariTall24 : Unit → IO Int := runPariAt (tall 24)
def runHexTall32 : Unit → IO Int := runHexAt (tall 32)
def runFlintTall32 : Unit → IO Int := runFlintAt (tall 32)
def runPariTall32 : Unit → IO Int := runPariAt (tall 32)
def runHexTall40 : Unit → IO Int := runHexAt (tall 40)
def runFlintTall40 : Unit → IO Int := runFlintAt (tall 40)
def runPariTall40 : Unit → IO Int := runPariAt (tall 40)
def runHexConjugate16 : Unit → IO Int := runHexAt (conjugate 16)
def runFlintConjugate16 : Unit → IO Int := runFlintAt (conjugate 16)
def runPariConjugate16 : Unit → IO Int := runPariAt (conjugate 16)
def runHexConjugate24 : Unit → IO Int := runHexAt (conjugate 24)
def runFlintConjugate24 : Unit → IO Int := runFlintAt (conjugate 24)
def runPariConjugate24 : Unit → IO Int := runPariAt (conjugate 24)
def runHexConjugate32 : Unit → IO Int := runHexAt (conjugate 32)
def runFlintConjugate32 : Unit → IO Int := runFlintAt (conjugate 32)
def runPariConjugate32 : Unit → IO Int := runPariAt (conjugate 32)
def runHexConjugate40 : Unit → IO Int := runHexAt (conjugate 40)
def runFlintConjugate40 : Unit → IO Int := runFlintAt (conjugate 40)
def runPariConjugate40 : Unit → IO Int := runPariAt (conjugate 40)

def runFlintOverhead (_ : Unit) : IO Int := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mat" "overhead" #[]
  match result.getInt? with
  | .ok value => return value
  | .error error => throw <| IO.userError s!"invalid FLINT overhead reply: {error}"

def runPariOverhead (_ : Unit) : IO Int := do
  let result ← Hex.BenchOracle.Pari.runOp "fmpz_mat" "overhead" #[]
  match result.getInt? with
  | .ok value => return value
  | .error error => throw <| IO.userError s!"invalid PARI overhead reply: {error}"

/- Cost-model derivation: the square dense family scans `n` columns, clears
`O(n)` rows per pivot, and each elementary row update touches `O(n)` entries,
giving `O(n³)` integer operations. -/
setup_benchmark runDense n => n ^ 3 with prep := dense where {
  paramFloor := 20, paramCeiling := 80, paramSchedule := .custom #[20, 32, 48, 64, 80]
  targetInnerNanos := 2_000_000_000
  maxSecondsPerCall := 10.0
}
/- Cost-model derivation: rank deficiency changes which pivots are found but
not the worst-case column, row-clear, and row-width loops, so the square
family remains `O(n³)` integer operations. -/
setup_benchmark runDeficient n => n ^ 3 with prep := deficient where {
  paramFloor := 20, paramCeiling := 80, paramSchedule := .custom #[20, 32, 48, 64, 80]
  targetInnerNanos := 2_000_000_000
  maxSecondsPerCall := 10.0
}
/- Cost-model derivation: the tall family has `4n` rows and `n` columns;
clearing `O(n)` rows with `O(n)`-wide updates for each of `n` columns is still
`O(n³)` integer operations because the aspect ratio is fixed. -/
setup_benchmark runTall n => n ^ 3 with prep := tall where {
  paramFloor := 8, paramCeiling := 24, paramSchedule := .custom #[8, 12, 16, 20, 24]
  targetInnerNanos := 2_000_000_000
  maxSecondsPerCall := 10.0
}
/- Cost-model derivation: conjugation changes coefficient growth but retains
the square `n`-column by `n`-row clearing structure with `n`-wide updates, so
the declared operation-count model is `O(n³)`. -/
setup_benchmark runConjugate n => n ^ 3 with prep := conjugate where {
  paramFloor := 20, paramCeiling := 80, paramSchedule := .custom #[20, 32, 48, 64, 80]
  targetInnerNanos := 2_000_000_000
  maxSecondsPerCall := 10.0
}

private def apiConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 3
  maxSecondsPerCall := 6.0

private def hexComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := 8.0

private def externalComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := 8.0
  warmupFirstIter := true

setup_fixed_benchmark runIsHNFForm where apiConfig
setup_fixed_benchmark runRank where apiConfig
setup_fixed_benchmark runBasis where apiConfig
setup_fixed_benchmark runData where apiConfig
setup_fixed_benchmark runWithInv where apiConfig
setup_fixed_benchmark runCoeffs where apiConfig
setup_fixed_benchmark runContains where apiConfig
setup_fixed_benchmark runKernelBasis where apiConfig
setup_fixed_benchmark runPivots where apiConfig
setup_fixed_benchmark runIndex where apiConfig
setup_fixed_benchmark runCert where apiConfig

setup_fixed_benchmark runFlintOverhead where externalComparisonConfig
setup_fixed_benchmark runPariOverhead where externalComparisonConfig
setup_fixed_benchmark runHexDense16 where hexComparisonConfig
setup_fixed_benchmark runFlintDense16 where externalComparisonConfig
setup_fixed_benchmark runPariDense16 where externalComparisonConfig
setup_fixed_benchmark runHexDense24 where hexComparisonConfig
setup_fixed_benchmark runFlintDense24 where externalComparisonConfig
setup_fixed_benchmark runPariDense24 where externalComparisonConfig
setup_fixed_benchmark runHexDense32 where hexComparisonConfig
setup_fixed_benchmark runFlintDense32 where externalComparisonConfig
setup_fixed_benchmark runPariDense32 where externalComparisonConfig
setup_fixed_benchmark runHexDense40 where hexComparisonConfig
setup_fixed_benchmark runFlintDense40 where externalComparisonConfig
setup_fixed_benchmark runPariDense40 where externalComparisonConfig
setup_fixed_benchmark runHexDeficient16 where hexComparisonConfig
setup_fixed_benchmark runFlintDeficient16 where externalComparisonConfig
setup_fixed_benchmark runPariDeficient16 where externalComparisonConfig
setup_fixed_benchmark runHexDeficient24 where hexComparisonConfig
setup_fixed_benchmark runFlintDeficient24 where externalComparisonConfig
setup_fixed_benchmark runPariDeficient24 where externalComparisonConfig
setup_fixed_benchmark runHexDeficient32 where hexComparisonConfig
setup_fixed_benchmark runFlintDeficient32 where externalComparisonConfig
setup_fixed_benchmark runPariDeficient32 where externalComparisonConfig
setup_fixed_benchmark runHexDeficient40 where hexComparisonConfig
setup_fixed_benchmark runFlintDeficient40 where externalComparisonConfig
setup_fixed_benchmark runPariDeficient40 where externalComparisonConfig
setup_fixed_benchmark runHexTall16 where hexComparisonConfig
setup_fixed_benchmark runFlintTall16 where externalComparisonConfig
setup_fixed_benchmark runPariTall16 where externalComparisonConfig
setup_fixed_benchmark runHexTall24 where hexComparisonConfig
setup_fixed_benchmark runFlintTall24 where externalComparisonConfig
setup_fixed_benchmark runPariTall24 where externalComparisonConfig
setup_fixed_benchmark runHexTall32 where hexComparisonConfig
setup_fixed_benchmark runFlintTall32 where externalComparisonConfig
setup_fixed_benchmark runPariTall32 where externalComparisonConfig
setup_fixed_benchmark runHexTall40 where hexComparisonConfig
setup_fixed_benchmark runFlintTall40 where externalComparisonConfig
setup_fixed_benchmark runPariTall40 where externalComparisonConfig
setup_fixed_benchmark runHexConjugate16 where hexComparisonConfig
setup_fixed_benchmark runFlintConjugate16 where externalComparisonConfig
setup_fixed_benchmark runPariConjugate16 where externalComparisonConfig
setup_fixed_benchmark runHexConjugate24 where hexComparisonConfig
setup_fixed_benchmark runFlintConjugate24 where externalComparisonConfig
setup_fixed_benchmark runPariConjugate24 where externalComparisonConfig
setup_fixed_benchmark runHexConjugate32 where hexComparisonConfig
setup_fixed_benchmark runFlintConjugate32 where externalComparisonConfig
setup_fixed_benchmark runPariConjugate32 where externalComparisonConfig
setup_fixed_benchmark runHexConjugate40 where hexComparisonConfig
setup_fixed_benchmark runFlintConjugate40 where externalComparisonConfig
setup_fixed_benchmark runPariConjugate40 where externalComparisonConfig

end Hex.HermiteBench

private def growthMain (args : List String) : IO UInt32 := do
  for arg in args do
    let some n := arg.toNat?
      | throw <| IO.userError s!"invalid growth dimension: {arg}"
    let (peak, output) := Hex.HermiteBench.conjugateGrowth n
    IO.println s!"n={n} peakBits={peak} outputBits={output}"
  return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | "growth" :: dimensions => growthMain dimensions
  | _ => LeanBench.Cli.dispatch args
