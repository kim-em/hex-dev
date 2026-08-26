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

private def denseShape (salt rows cols : Nat) : Input :=
  { rows := rows, cols := cols
    entries := (Array.range (rows * cols)).map fun k =>
      let i := k / cols
      let j := k % cols
      noise salt (rows + cols) i j +
        if i = j then Int.ofNat (32 * max rows cols + 1) else 0 }

/-- Uniform-looking dense, diagonally shifted square input. -/
def dense (n : Nat) : Input := denseShape 7 n n

/-- Dense tall input with fixed aspect ratio and full column rank. -/
def denseTall (n : Nat) : Input := denseShape 11 (2 * n) n

/-- Dense wide input with fixed aspect ratio and full row rank. -/
def denseWide (n : Nat) : Input := denseShape 13 n (2 * n)

/-- Dense square input whose lower half repeats its upper half. -/
def denseDeficient (n : Nat) : Input :=
  let rank := max 1 (n / 2)
  { rows := n, cols := n
    entries := (Array.range (n * n)).map fun k =>
      let i := (k / n) % rank
      let j := k % n
      noise 17 n i j + if i = j then Int.ofNat (32 * n + 1) else 0 }

private def chainShape (rows cols rank : Nat) : Input :=
  { rows := rows, cols := cols
    entries := (Array.range (rows * cols)).map fun k =>
      let i := k / cols
      let j := k % cols
      (List.range rank).foldl (fun acc t =>
        let u : Int := if t = i then 1 else if t < i then noise 19 rank i t else 0
        let d : Int := Int.ofNat (2 ^ (t + 1))
        let v : Int := if t = j then 1 else if j < t then noise 23 rank t j else 0
        acc + u * d * v) 0 }

/-- A known full-rank chain conjugated by unit triangular matrices. -/
def chainConjugate (n : Nat) : Input := chainShape n n n

/-- A known conjugated chain with a linear-sized zero tail. -/
def chainDeficient (n : Nat) : Input := chainShape n n (n - n / 4)

private def presentationShape (rows cols : Nat) : Input :=
  { rows := rows, cols := cols
    entries := (Array.range (rows * cols)).map fun k =>
      let i := k / cols
      let j := k % cols
      if i = j then Int.ofNat (2 * (i + 1))
      else if j + 1 = i then -1
      else if i + 2 = j then 1
      else 0 }

/-- Sparse square relation matrix with a handful of mixed generators. -/
def presentation (n : Nat) : Input := presentationShape n n

/-- Sparse presentation with two more generators than relations. -/
def presentationWide (n : Nat) : Input := presentationShape n (n + 2)

private def matrix (input : Input) : Matrix Int input.rows input.cols :=
  Matrix.ofFn fun i j => input.entries.getD (i.val * input.cols + j.val) 0

private def checksum (M : Matrix Int n m) : UInt64 :=
  M.data.foldl (fun acc x => mixHash acc (hash x)) 0

private def dataChecksum (D : Matrix.SmithData n m) : UInt64 :=
  let diagonal := D.diag.toList.foldl (fun acc x => mixHash acc (hash x)) 0
  mixHash (checksum D.left) <| mixHash (checksum D.leftInv) <|
    mixHash (checksum D.right) (mixHash (checksum D.rightInv) diagonal)

/- Alternating units and twos force quadratically many adjacent repairs while
keeping operand width bounded; the trailing zero exercises rank deficiency. -/
private def diagonal (n : Nat) : Vector Int n :=
  Vector.ofFn fun i => if i.val + 1 = n then 0
    else if i.val % 2 = 0 then 2 else -1

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

private def emitGrowth (family shape : String) (n : Nat) (input : Input) : IO Unit := do
  let A := matrix input
  let form := Matrix.snf A
  let peak := peakBits input
  IO.println s!"{family},{shape},{n},{input.rows},{input.cols},{peak},{matrixBits form}"

/-- Emit untimed entry-growth diagnostics for every declared family and shape. -/
def growthReport : IO UInt32 := do
  IO.println "family,shape,n,rows,cols,peak_bits,output_bits"
  for n in #[2, 4, 6, 8, 10, 12] do
    emitGrowth "random-dense-smith" "square" n (dense n)
    emitGrowth "random-dense-smith" "tall-2x1" n (denseTall n)
    emitGrowth "random-dense-smith" "wide-1x2" n (denseWide n)
    emitGrowth "random-dense-smith" "rank-deficient" n (denseDeficient n)
    emitGrowth "chain-conjugate" "square" n (chainConjugate n)
    emitGrowth "chain-conjugate" "rank-deficient" n (chainDeficient n)
  for n in #[2, 4, 8, 12, 16, 24] do
    emitGrowth "presentation-smith" "square" n (presentation n)
    emitGrowth "presentation-smith" "wide" n (presentationWide n)
  return 0

def runDense (input : Input) : UInt64 := checksum (Matrix.snf (matrix input))
def runDenseTall (input : Input) : UInt64 := checksum (Matrix.snf (matrix input))
def runDenseWide (input : Input) : UInt64 := checksum (Matrix.snf (matrix input))
def runDenseDeficient (input : Input) : UInt64 := checksum (Matrix.snf (matrix input))
def runChain (input : Input) : UInt64 := checksum (Matrix.snf (matrix input))
def runChainDeficient (input : Input) : UInt64 := checksum (Matrix.snf (matrix input))
def runPresentation (input : Input) : UInt64 := checksum (Matrix.snf (matrix input))
def runPresentationWide (input : Input) : UInt64 := checksum (Matrix.snf (matrix input))
def runRank (input : Input) : Nat := Matrix.snfRank (matrix input)
def runInvariantFactors (input : Input) : UInt64 :=
  (Matrix.invariantFactors (matrix input)).toList.foldl
    (fun acc d => mixHash acc (hash d)) 0
def runData (input : Input) : UInt64 := dataChecksum (Matrix.snfData (matrix input))
def runSmithBasis (input : Input) : UInt64 := checksum (Matrix.smithBasis (matrix input))
def runAbelianStructure (input : Input) : UInt64 :=
  let result := Matrix.abelianStructure (matrix input)
  result.torsionFactors.foldl (fun acc d => mixHash acc (hash d)) (hash result.freeRank)
def runDiagonal (n : Nat) : UInt64 := checksum (Matrix.snfDiagonal (diagonal n))
def runDiagonalGeneral (n : Nat) : UInt64 :=
  checksum (Matrix.snf (Matrix.diagMatrix (diagonal n) n n))
def runDiagonalData (n : Nat) : UInt64 := dataChecksum (Matrix.snfDiagonalData (diagonal n))

/-- A valid certificate prepared outside the checker's timed region. -/
structure CertInput where
  n : Nat
  matrix : Matrix Int n n
  data : Matrix.SmithData n n
  intermediate : Matrix Int n n

instance : Hashable CertInput where
  hash input := mixHash (hash input.n)
    (mixHash (hash (checksum input.matrix))
      (mixHash (hash (dataChecksum input.data)) (hash (checksum input.intermediate))))

instance : Inhabited CertInput := by
  let I : Matrix Int 0 0 := Matrix.identity 0
  let d : Vector Int 0 := Vector.ofFn fun i => nomatch i
  let S : Matrix.SmithData 0 0 :=
    { rank := 0, diag := d, left := I, leftInv := I, right := I, rightInv := I }
  exact ⟨CertInput.mk 0 I S I⟩

/-- Prepare the certificate for `diag(2,…,2)` without running Smith reduction. -/
def certInput (n : Nat) : CertInput :=
  let d : Vector Int n := Vector.ofFn fun _ => 2
  let A := Matrix.diagMatrix d n n
  let I : Matrix Int n n := Matrix.identity n
  { n := n, matrix := A,
    data := { rank := n, diag := d, left := I, leftInv := I, right := I, rightInv := I },
    intermediate := A }

def runShape (input : CertInput) : Bool := Matrix.isSNFShape input.data
def runCert (input : CertInput) : Bool :=
  Matrix.snfCert input.matrix input.data input.intermediate

private def inputRowsJson (input : Input) : Lean.Json :=
  Lean.Json.arr (Array.ofFn fun i : Fin input.rows =>
    Hex.BenchOracle.Flint.intsToJson
      (List.ofFn fun j : Fin input.cols =>
        input.entries.getD (i.val * input.cols + j.val) 0))

private def runHexAt (input : Input) (_ : Unit) : IO (List Int) :=
  return (Matrix.invariantFactors (matrix input)).toList

private def runFlintAt (input : Input) (_ : Unit) : IO (List Int) := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mat" "snf"
    #[("rows", inputRowsJson input)]
  Hex.BenchOracle.Flint.jsonToInts result

private def runPariAt (input : Input) (_ : Unit) : IO (List Int) := do
  let result ← Hex.BenchOracle.Pari.runOp "fmpz_mat" "snf"
    #[("rows", inputRowsJson input)]
  Hex.BenchOracle.Flint.jsonToInts result

def runHexDense6 : Unit → IO (List Int) := runHexAt (dense 6)
def runFlintDense6 : Unit → IO (List Int) := runFlintAt (dense 6)
def runPariDense6 : Unit → IO (List Int) := runPariAt (dense 6)
def runHexDense8 : Unit → IO (List Int) := runHexAt (dense 8)
def runFlintDense8 : Unit → IO (List Int) := runFlintAt (dense 8)
def runPariDense8 : Unit → IO (List Int) := runPariAt (dense 8)
def runHexDense10 : Unit → IO (List Int) := runHexAt (dense 10)
def runFlintDense10 : Unit → IO (List Int) := runFlintAt (dense 10)
def runPariDense10 : Unit → IO (List Int) := runPariAt (dense 10)
def runHexDense12 : Unit → IO (List Int) := runHexAt (dense 12)
def runFlintDense12 : Unit → IO (List Int) := runFlintAt (dense 12)
def runPariDense12 : Unit → IO (List Int) := runPariAt (dense 12)
def runHexDense14 : Unit → IO (List Int) := runHexAt (dense 14)
def runFlintDense14 : Unit → IO (List Int) := runFlintAt (dense 14)
def runPariDense14 : Unit → IO (List Int) := runPariAt (dense 14)
def runHexChain6 : Unit → IO (List Int) := runHexAt (chainConjugate 6)
def runFlintChain6 : Unit → IO (List Int) := runFlintAt (chainConjugate 6)
def runPariChain6 : Unit → IO (List Int) := runPariAt (chainConjugate 6)
def runHexChain8 : Unit → IO (List Int) := runHexAt (chainConjugate 8)
def runFlintChain8 : Unit → IO (List Int) := runFlintAt (chainConjugate 8)
def runPariChain8 : Unit → IO (List Int) := runPariAt (chainConjugate 8)
def runHexChain10 : Unit → IO (List Int) := runHexAt (chainConjugate 10)
def runFlintChain10 : Unit → IO (List Int) := runFlintAt (chainConjugate 10)
def runPariChain10 : Unit → IO (List Int) := runPariAt (chainConjugate 10)
def runHexChain12 : Unit → IO (List Int) := runHexAt (chainConjugate 12)
def runFlintChain12 : Unit → IO (List Int) := runFlintAt (chainConjugate 12)
def runPariChain12 : Unit → IO (List Int) := runPariAt (chainConjugate 12)
def runHexChain14 : Unit → IO (List Int) := runHexAt (chainConjugate 14)
def runFlintChain14 : Unit → IO (List Int) := runFlintAt (chainConjugate 14)
def runPariChain14 : Unit → IO (List Int) := runPariAt (chainConjugate 14)
def runHexPresentation8 : Unit → IO (List Int) := runHexAt (presentation 8)
def runFlintPresentation8 : Unit → IO (List Int) := runFlintAt (presentation 8)
def runPariPresentation8 : Unit → IO (List Int) := runPariAt (presentation 8)
def runHexPresentation12 : Unit → IO (List Int) := runHexAt (presentation 12)
def runFlintPresentation12 : Unit → IO (List Int) := runFlintAt (presentation 12)
def runPariPresentation12 : Unit → IO (List Int) := runPariAt (presentation 12)
def runHexPresentation16 : Unit → IO (List Int) := runHexAt (presentation 16)
def runFlintPresentation16 : Unit → IO (List Int) := runFlintAt (presentation 16)
def runPariPresentation16 : Unit → IO (List Int) := runPariAt (presentation 16)
def runHexPresentation20 : Unit → IO (List Int) := runHexAt (presentation 20)
def runFlintPresentation20 : Unit → IO (List Int) := runFlintAt (presentation 20)
def runPariPresentation20 : Unit → IO (List Int) := runPariAt (presentation 20)
def runHexPresentation24 : Unit → IO (List Int) := runHexAt (presentation 24)
def runFlintPresentation24 : Unit → IO (List Int) := runFlintAt (presentation 24)
def runPariPresentation24 : Unit → IO (List Int) := runPariAt (presentation 24)

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

/- The form-only pivot loop performs `O(n)` stages, each scanning/updating an
`O(n²)` trailing block when entry bit-width and the repeat factor are controlled. -/
setup_benchmark runDense n => n ^ 3 with prep := dense where {
  paramFloor := 4, paramCeiling := 14, paramSchedule := .custom #[4, 6, 8, 10, 12, 14]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  signalFloorMultiplier := 1.0, outerTrials := 3
}

/- At fixed 2:1 aspect ratio, the rectangular pivot loop still has `O(n)`
stages updating `O(n²)` entries, so the matrix-update model is cubic. -/
setup_benchmark runDenseTall n => n ^ 3 with prep := denseTall where {
  paramFloor := 3, paramCeiling := 10, paramSchedule := .custom #[3, 4, 5, 6, 8, 10]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  signalFloorMultiplier := 1.0, outerTrials := 3
}

/- At fixed 1:2 aspect ratio, `O(n)` pivots update an `O(n²)` trailing
rectangle; hashing the `n × 2n` result remains lower-order than the cubic run. -/
setup_benchmark runDenseWide n => n ^ 3 with prep := denseWide where {
  paramFloor := 3, paramCeiling := 10, paramSchedule := .custom #[3, 4, 5, 6, 8, 10]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  signalFloorMultiplier := 1.0, outerTrials := 3
}

/- Repeating the lower half fixes rank at `Θ(n)` while retaining `O(n)`
pivot stages and `O(n²)` scans/updates, hence the cubic matrix-update model. -/
setup_benchmark runDenseDeficient n => n ^ 3 with prep := denseDeficient where {
  paramFloor := 4, paramCeiling := 14, paramSchedule := .custom #[4, 6, 8, 10, 12, 14]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  signalFloorMultiplier := 1.0, outerTrials := 3
}

/- Conjugation changes entries but not the `O(n)`-stage, `O(n²)`-update
classical schedule when the controlled chain family bounds the repeat regime. -/
setup_benchmark runChain n => n ^ 3 with prep := chainConjugate where {
  paramFloor := 4, paramCeiling := 14, paramSchedule := .custom #[4, 6, 8, 10, 12, 14]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  signalFloorMultiplier := 1.0, outerTrials := 3
}

/- The conjugated zero tail leaves rank `Θ(n)` and therefore the same
`O(n)` stages of `O(n²)` dense updates as the full chain family. -/
setup_benchmark runChainDeficient n => n ^ 3 with prep := chainDeficient where {
  paramFloor := 4, paramCeiling := 14, paramSchedule := .custom #[4, 6, 8, 10, 12, 14]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  signalFloorMultiplier := 1.0, outerTrials := 3
}

/- V1 deliberately sends sparse square presentations through `O(n)` stages
of dense `O(n²)` matrix updates, giving the cubic model. -/
setup_benchmark runPresentation n => n ^ 3 with prep := presentation where {
  paramFloor := 16, paramCeiling := 96, paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  verdictWarmupFraction := 0.3, signalFloorMultiplier := 1.0, outerTrials := 3
}

/- With two extra generators the presentation aspect ratio tends to one, so
`O(n)` stages still perform `O(n²)` dense updates. -/
setup_benchmark runPresentationWide n => n ^ 3 with prep := presentationWide where {
  paramFloor := 16, paramCeiling := 96, paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  verdictWarmupFraction := 0.3, signalFloorMultiplier := 1.0, outerTrials := 3
}

/- `snfRank` projects the result of exactly the form-only cubic pivot run. -/
setup_benchmark runRank n => n ^ 3 with prep := dense where {
  paramFloor := 4, paramCeiling := 14, paramSchedule := .custom #[4, 6, 8, 10, 12, 14]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  signalFloorMultiplier := 1.0, outerTrials := 3
}

/- `invariantFactors` projects and hashes `O(n)` diagonal entries after the
same cubic form-only run; the structural hash is lower-order. -/
setup_benchmark runInvariantFactors n => n ^ 3 with prep := dense where {
  paramFloor := 4, paramCeiling := 14, paramSchedule := .custom #[4, 6, 8, 10, 12, 14]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  signalFloorMultiplier := 1.0, outerTrials := 3
}

/- Accumulating and hashing four dense transforms adds `O(n³)` scalar-entry
work to the cubic pivot run. -/
setup_benchmark runData n => n ^ 3 with prep := dense where {
  paramFloor := 4, paramCeiling := 12, paramSchedule := .custom #[4, 6, 8, 10, 12]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  signalFloorMultiplier := 1.0, outerTrials := 3
}

/- `smithBasis` performs the cubic transform-producing run and one dense
matrix product; hashing its `O(n²)` output is lower-order. -/
setup_benchmark runSmithBasis n => n ^ 3 with prep := dense where {
  paramFloor := 4, paramCeiling := 12, paramSchedule := .custom #[4, 6, 8, 10, 12]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  signalFloorMultiplier := 1.0, outerTrials := 3
}

/- `abelianStructure` is the cubic form-only run followed by an `O(n)` filter
and structural hash of the torsion factors. -/
setup_benchmark runAbelianStructure n => n ^ 3 with prep := presentationWide where {
  paramFloor := 16, paramCeiling := 96, paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  verdictWarmupFraction := 0.3, signalFloorMultiplier := 1.0, outerTrials := 3
}

/- `isSNFShape` scans `n` positive diagonal entries and `n-1` adjacent
divisibility obligations on a certificate prepared outside the timed body. -/
setup_benchmark runShape n => n with prep := certInput where {
  paramFloor := 32, paramCeiling := 1024,
  paramSchedule := .custom #[32, 64, 128, 256, 512, 1024]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  signalFloorMultiplier := 1.0, outerTrials := 3
}

/- `snfCert` uses four packed product-equality checks. Each packs `O(n)` rows
and performs `O(n²)` big-by-small operations; packed operands carry `O(n)`
bits on this bounded-entry family, recorded separately from the operation count. -/
setup_benchmark runCert n => n ^ 2 with prep := certInput where {
  paramFloor := 16, paramCeiling := 96, paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  verdictWarmupFraction := 0.5, signalFloorMultiplier := 1.0, outerTrials := 3
}

/- The diagonal fast path performs `n` adjacent passes, each containing
`O(n)` gcd/lcm pair steps, and never allocates dense transforms. -/
setup_benchmark runDiagonal n => n ^ 2 where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom #[8, 12, 16, 24, 32, 48, 64]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  signalFloorMultiplier := 1.0, outerTrials := 3
}

/- The general route executes `O(n)` pivot stages over dense matrices and is
registered with its conservative cubic matrix-update model. -/
setup_benchmark runDiagonalGeneral n => n ^ 3 where {
  paramFloor := 8, paramCeiling := 64, paramSchedule := .custom #[8, 12, 16, 24, 32, 48, 64]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  signalFloorMultiplier := 1.0, outerTrials := 3
}

/- The quadratic pair network updates four dense transform matrices at every
step, for `O(n³)` scalar-entry work and `O(n²)` result hashing. -/
setup_benchmark runDiagonalData n => n ^ 3 where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  maxSecondsPerCall := 10.0, targetInnerNanos := 100000000,
  verdictWarmupFraction := 0.5, signalFloorMultiplier := 1.0, outerTrials := 3
}

private def hexComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := 10.0

private def externalComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := 10.0
  warmupFirstIter := true

private def hexExpected (expected : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { hexComparisonConfig with expectedHash := some expected }

private def externalExpected (expected : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { externalComparisonConfig with expectedHash := some expected }

setup_fixed_benchmark runFlintOverhead where externalExpected 0x0
setup_fixed_benchmark runPariOverhead where externalExpected 0x0
setup_fixed_benchmark runHexDense6 where hexExpected 0xf04520317df0def8
setup_fixed_benchmark runFlintDense6 where externalExpected 0xf04520317df0def8
setup_fixed_benchmark runPariDense6 where externalExpected 0xf04520317df0def8
setup_fixed_benchmark runHexDense8 where hexExpected 0xe4073bf661a3c59a
setup_fixed_benchmark runFlintDense8 where externalExpected 0xe4073bf661a3c59a
setup_fixed_benchmark runPariDense8 where externalExpected 0xe4073bf661a3c59a
setup_fixed_benchmark runHexDense10 where hexExpected 0xf68ae7878c8af87b
setup_fixed_benchmark runFlintDense10 where externalExpected 0xf68ae7878c8af87b
setup_fixed_benchmark runPariDense10 where externalExpected 0xf68ae7878c8af87b
setup_fixed_benchmark runHexDense12 where hexExpected 0x5e971675ada9d783
setup_fixed_benchmark runFlintDense12 where externalExpected 0x5e971675ada9d783
setup_fixed_benchmark runPariDense12 where externalExpected 0x5e971675ada9d783
setup_fixed_benchmark runHexDense14 where hexExpected 0x699fd5ab6f700da0
setup_fixed_benchmark runFlintDense14 where externalExpected 0x699fd5ab6f700da0
setup_fixed_benchmark runPariDense14 where externalExpected 0x699fd5ab6f700da0
setup_fixed_benchmark runHexChain6 where hexExpected 0x1e5b9e22113b8d71
setup_fixed_benchmark runFlintChain6 where externalExpected 0x1e5b9e22113b8d71
setup_fixed_benchmark runPariChain6 where externalExpected 0x1e5b9e22113b8d71
setup_fixed_benchmark runHexChain8 where hexExpected 0xb3713c08af9eb87c
setup_fixed_benchmark runFlintChain8 where externalExpected 0xb3713c08af9eb87c
setup_fixed_benchmark runPariChain8 where externalExpected 0xb3713c08af9eb87c
setup_fixed_benchmark runHexChain10 where hexExpected 0xefcb83d9d11c9839
setup_fixed_benchmark runFlintChain10 where externalExpected 0xefcb83d9d11c9839
setup_fixed_benchmark runPariChain10 where externalExpected 0xefcb83d9d11c9839
setup_fixed_benchmark runHexChain12 where hexExpected 0x239317e249e653d3
setup_fixed_benchmark runFlintChain12 where externalExpected 0x239317e249e653d3
setup_fixed_benchmark runPariChain12 where externalExpected 0x239317e249e653d3
setup_fixed_benchmark runHexChain14 where hexExpected 0x049888f934ad3581
setup_fixed_benchmark runFlintChain14 where externalExpected 0x049888f934ad3581
setup_fixed_benchmark runPariChain14 where externalExpected 0x049888f934ad3581
setup_fixed_benchmark runHexPresentation8 where hexExpected 0x82b42ad65a90f9be
setup_fixed_benchmark runFlintPresentation8 where externalExpected 0x82b42ad65a90f9be
setup_fixed_benchmark runPariPresentation8 where externalExpected 0x82b42ad65a90f9be
setup_fixed_benchmark runHexPresentation12 where hexExpected 0xfc1472e454f53028
setup_fixed_benchmark runFlintPresentation12 where externalExpected 0xfc1472e454f53028
setup_fixed_benchmark runPariPresentation12 where externalExpected 0xfc1472e454f53028
setup_fixed_benchmark runHexPresentation16 where hexExpected 0x47ef2f14529c425f
setup_fixed_benchmark runFlintPresentation16 where externalExpected 0x47ef2f14529c425f
setup_fixed_benchmark runPariPresentation16 where externalExpected 0x47ef2f14529c425f
setup_fixed_benchmark runHexPresentation20 where hexExpected 0x032c9800f08ccd0d
setup_fixed_benchmark runFlintPresentation20 where externalExpected 0x032c9800f08ccd0d
setup_fixed_benchmark runPariPresentation20 where externalExpected 0x032c9800f08ccd0d
setup_fixed_benchmark runHexPresentation24 where hexExpected 0xb281650658ac39a7
setup_fixed_benchmark runFlintPresentation24 where externalExpected 0xb281650658ac39a7
setup_fixed_benchmark runPariPresentation24 where externalExpected 0xb281650658ac39a7

end Hex.SmithBench

def main (args : List String) : IO UInt32 :=
  match args with
  | ["growth"] => Hex.SmithBench.growthReport
  | _ => LeanBench.Cli.dispatch args
