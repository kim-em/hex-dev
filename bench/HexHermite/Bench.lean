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

private def lowerFactor (n i j : Nat) : Int :=
  if i = j then 1
  else if j < i then if entry 41 n i j < 0 then -1 else 1
  else 0

private def upperFactor (n i j : Nat) : Int :=
  if i = j then 1
  else if i < j then if entry 43 n i j < 0 then -1 else 1
  else 0

/-- A deterministic pseudo-random unimodular product `L * U * D`. Both
triangular factors vary, while `D` fixes the expected row lattice. -/
def conjugate (n : Nat) : Input :=
  { rows := n, cols := n
    entries := (Array.range (n * n)).map fun k =>
      let i := k / n
      let j := k % n
      let vij := (List.range n).foldl (fun acc t =>
        acc + lowerFactor n i t * upperFactor n t j) 0
      vij * Int.ofNat (j + 2) }

private def matrix (input : Input) : Matrix Int input.rows input.cols :=
  Matrix.ofFn fun i j => input.entries.getD (i.val * input.cols + j.val) 0

/- A fixed-width structural checksum keeps result observation linear in the
matrix size without making the benchmark multiply ever-growing `Int` values. -/
private def checksum (M : Matrix Int n m) : UInt64 :=
  M.data.foldl (fun acc x => mixHash acc (hash x)) 0

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

private def growthNormalize (s : GrowthState n m) (col : Fin m)
    (pivot : Fin n) : GrowthState n m :=
  if s.result.matrix[(pivot, col)] = 0 then s else
    let ops := Matrix.Hermite.formAccumulator n
    let s := observe (Matrix.Hermite.signStep ops col pivot s.result) s.peak
    (List.finRange n).foldl (fun s row =>
      if row.val < pivot.val then
        observe (Matrix.Hermite.reduceStep ops col pivot row s.result) s.peak
      else s) s

private def growthPrior (pivots : List (Fin m)) (row : Fin n)
    (s : GrowthState n m) (pivot : Fin n) : GrowthState n m :=
  if pivot.val < row.val then
    if hp : pivot.val < pivots.length then
      let col := pivots.get ⟨pivot.val, hp⟩
      let next := Matrix.Hermite.gcdStep (Matrix.Hermite.formAccumulator n)
        col pivot row s.result
      growthNormalize (observe next s.peak) col pivot
    else s
  else s

private def growthAdmit (pivots : List (Fin m)) (s : GrowthState n m)
    (row : Fin n) : GrowthState n m :=
  let s := (List.finRange n).foldl (growthPrior pivots row) s
  if hp : row.val < pivots.length then
    growthNormalize s (pivots.get ⟨row.val, hp⟩) row
  else s

private def principalGrowth (A : Matrix Int n m) : GrowthState n m :=
  let profile := Matrix.Hermite.rankProfile A
  let initial : GrowthState n m :=
    { result :=
        { matrix := A, pivots := profile.pivots
          accumulator := (Matrix.Hermite.formAccumulator n).init }
      peak := matrixBits A }
  let permuted := profile.swaps.foldl (fun s swap =>
    observe (Matrix.Hermite.swapStep (Matrix.Hermite.formAccumulator n)
      s.result swap.1 swap.2) s.peak) initial
  (List.finRange n).foldl (growthAdmit profile.pivots) permuted

private def columnGrowth (A : Matrix Int n m) : GrowthState n m :=
  let initial : GrowthState n m :=
    { result :=
        { matrix := A, pivots := []
          accumulator := (Matrix.Hermite.formAccumulator n).init }
      peak := matrixBits A }
  (List.finRange m).foldl growthColumn initial

/-- Scan the working matrix after every elementary update and return the peak
coefficient bit-size. This runner is intentionally separate from timed
benchmarks so instrumentation does not perturb ordinary timings. -/
def peakBits (input : Input) : Nat :=
  let A := matrix input
  let candidate := principalGrowth A
  if Matrix.isHNFForm candidate.result.matrix candidate.result.pivots.length
      candidate.result.pivotVector then
    candidate.peak
  else
    (columnGrowth A).peak

/-- Peak-versus-output growth data, including a check that the instrumented
schedule finishes at the public uninstrumented result. -/
def growthData (input : Input) : Nat × Nat × Bool :=
  let A := matrix input
  let candidate := principalGrowth A
  let result := if Matrix.isHNFForm candidate.result.matrix candidate.result.pivots.length
      candidate.result.pivotVector then candidate else columnGrowth A
  let H := Matrix.hnf A
  (result.peak, matrixBits H, result.result.matrix == H)

def runDense (input : Input) : UInt64 := checksum (Matrix.hnf (matrix input))
def runDeficient (input : Input) : UInt64 := checksum (Matrix.hnf (matrix input))
def runTall (input : Input) : UInt64 := checksum (Matrix.hnf (matrix input))
def runConjugate (input : Input) : UInt64 := checksum (Matrix.hnf (matrix input))

private def vectorChecksum (v : Vector Int n) : UInt64 :=
  v.foldl (fun acc x => mixHash acc (hash x)) 0

/-- Fraction-free rank-profile work, registered separately because profiling
identifies it as a dominant separable phase of `hnf`. -/
def runProfile (input : Input) : UInt64 :=
  let profile := Matrix.Hermite.rankProfile (matrix input)
  let pivots := profile.pivots.foldl (fun acc x => mixHash acc (hash x)) 0
  let swaps := profile.swaps.foldl (fun acc x =>
    mixHash acc (mixHash (hash x.1) (hash x.2))) 0
  mixHash (checksum profile.matrix) <|
    mixHash pivots (mixHash swaps (mixHash (hash profile.row) (hash profile.previous)))

/-- Dense matrix and precomputed rank profile for isolating the principal HNF
phase from its fraction-free preparation. -/
structure PrincipalInput where
  n : Nat
  form : Matrix Int n n
  profile : Matrix.Hermite.Profile n n

instance : Hashable PrincipalInput where
  hash input :=
    let pivots := input.profile.pivots.foldl
      (fun acc x => mixHash acc (hash x)) 0
    let swaps := input.profile.swaps.foldl (fun acc x =>
      mixHash acc (mixHash (hash x.1) (hash x.2))) 0
    mixHash (hash input.n) <|
      mixHash (checksum input.form) <|
      mixHash (checksum input.profile.matrix) <|
      mixHash pivots <| mixHash swaps <|
      mixHash (hash input.profile.row) (hash input.profile.previous)

instance : Inhabited PrincipalInput where
  default :=
    { n := 0
      form := 0
      profile := Matrix.Hermite.rankProfile (0 : Matrix Int 0 0) }

def principalInput (n : Nat) : PrincipalInput :=
  let A := matrix (dense n)
  { n, form := A, profile := Matrix.Hermite.rankProfile A }

/-- Principal-block reduction with rank profiling prepared outside the timed
region. -/
def runPrincipalDense (input : PrincipalInput) : UInt64 :=
  let result := Matrix.Hermite.principalCore
    (Matrix.Hermite.formAccumulator input.n) input.form input.profile
  mixHash (checksum result.matrix) <|
    result.pivots.foldl (fun acc x => mixHash acc (hash x)) 0

/-- Rank projection on the dense family. -/
def runRankDense (input : Input) : Nat := Matrix.hnfRank (matrix input)

/-- Canonical nonzero HNF rows on the dense family. -/
def runBasisDense (input : Input) : UInt64 := checksum (Matrix.hnfBasis (matrix input))

/-- Transform-producing HNF data on the dense family. -/
def runDataDense (input : Input) : UInt64 :=
  let D := Matrix.hnfData (matrix input)
  mixHash (checksum D.echelon) <| mixHash (checksum D.transform) (hash D.rank)

/-- Transform and inverse accumulation on the dense family. -/
def runWithInvDense (input : Input) : UInt64 :=
  let D := Matrix.hnfWithInv (matrix input)
  mixHash (checksum D.rowData.echelon) <|
    mixHash (checksum D.rowData.transform) (checksum D.inverse)

/-- Constructive membership coefficients for a known member. -/
def runCoeffsDense (input : Input) : UInt64 :=
  let A := matrix input
  let v : Vector Int input.cols :=
    if h : 0 < input.rows then Matrix.row A ⟨0, h⟩ else 0
  match Matrix.latticeCoeffs A v with
  | some c => mixHash (vectorChecksum v) (vectorChecksum c)
  | none => 0

/-- Membership decision for a known member, with the query included in the
observed result. -/
def runContainsDense (input : Input) : UInt64 :=
  let A := matrix input
  let v : Vector Int input.cols :=
    if h : 0 < input.rows then Matrix.row A ⟨0, h⟩ else 0
  mixHash (vectorChecksum v) (hash (Matrix.latticeContains A v))

/-- Kernel extraction on the rank-deficient family. -/
def runKernelDeficient (input : Input) : UInt64 :=
  checksum (Matrix.kernelBasis (matrix input))

/-- Pivot extraction on the dense family. -/
def runPivotsDense (input : Input) : UInt64 :=
  (Matrix.pivots (matrix input)).foldl (fun acc x => mixHash acc (hash x)) 0

/-- Lattice-index projection on the dense family. -/
def runIndexDense (input : Input) : Nat := Matrix.latticeIndex (matrix input)

/-- Valid bounded HNF data prepared outside the shape-checker timings. -/
structure ShapeInput where
  n : Nat
  form : Matrix Int n n
  pivots : Vector (Fin n) n

instance : Hashable ShapeInput where
  hash input := mixHash (hash input.n) <|
    mixHash (checksum input.form)
      (input.pivots.foldl (fun acc x => mixHash acc (hash x)) 0)

instance : Inhabited ShapeInput where
  default :=
    { n := 0
      form := 0
      pivots := Vector.ofFn fun i => nomatch i }

def shapeInput (n : Nat) : ShapeInput :=
  { n := n
    form := Matrix.ofFn fun i j => if i = j then Int.ofNat (i.val + 1) else 0
    pivots := Vector.ofFn id }

def runShapePrepared (input : ShapeInput) : Bool :=
  Matrix.isHNFForm input.form input.n input.pivots

/-- A nontrivial bounded unimodular certificate prepared outside replay timings. -/
structure CertInput where
  n : Nat
  source : Matrix Int n n
  form : Matrix Int n n
  transform : Matrix Int n n
  inverse : Matrix Int n n
  pivots : Vector (Fin n) n

instance : Hashable CertInput where
  hash input := mixHash (hash input.n) <|
    mixHash (checksum input.source) <|
    mixHash (checksum input.form) <|
    mixHash (checksum input.transform) <|
    mixHash (checksum input.inverse)
      (input.pivots.foldl (fun acc x => mixHash acc (hash x)) 0)

instance : Inhabited CertInput where
  default :=
    { n := 0
      source := 0
      form := 0
      transform := 0
      inverse := 0
      pivots := Vector.ofFn fun i => nomatch i }

def certInput (n : Nat) : CertInput :=
  let form : Matrix Int n n :=
    Matrix.ofFn fun i j => if i = j then Int.ofNat (i.val + 1) else 0
  let transform : Matrix Int n n := Matrix.ofFn fun i j =>
    if i = j then 1 else if i.val = j.val + 1 then 1 else 0
  let inverse : Matrix Int n n := Matrix.ofFn fun i j =>
    if j.val ≤ i.val then if (i.val - j.val) % 2 = 0 then 1 else -1 else 0
  let source : Matrix Int n n := Matrix.ofFn fun i j =>
    if j.val ≤ i.val then
      if (i.val - j.val) % 2 = 0 then Int.ofNat (j.val + 1) else -Int.ofNat (j.val + 1)
    else 0
  { n, source, form, transform, inverse, pivots := Vector.ofFn id }

def runCertPrepared (input : CertInput) : Bool :=
  Matrix.hnfCert input.source input.form input.transform input.inverse input.n input.pivots

#guard runShapePrepared (shapeInput 16)
#guard runCertPrepared (certInput 8)

private def fixedMatrix : Matrix Int 8 8 := matrix (dense 8)

private def fixedDeficientMatrix : Matrix Int 8 8 := matrix (deficient 8)

private def missMatrix : Matrix Int 1 2 :=
  Matrix.ofFn fun _ j => if j.val = 0 then 1 else 0

private def missVector : Vector Int 2 :=
  Vector.ofFn fun j => if j.val = 0 then 0 else 1

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

def runBasis (_ : Unit) : IO UInt64 := do
  let A ← live fixedMatrix
  return checksum (Matrix.hnfBasis A)

def runData (_ : Unit) : IO UInt64 := do
  let A ← live fixedMatrix
  let D := Matrix.hnfData A
  return mixHash (checksum D.echelon) <| mixHash (checksum D.transform) (hash D.rank)

def runWithInv (_ : Unit) : IO UInt64 := do
  let A ← live fixedMatrix
  let D := Matrix.hnfWithInv A
  return mixHash (checksum D.rowData.echelon) <|
    mixHash (checksum D.rowData.transform) (checksum D.inverse)

def runCoeffs (_ : Unit) : IO UInt64 := do
  let A ← live fixedMatrix
  return match Matrix.latticeCoeffs A (Matrix.row A 0) with
    | some c => mixHash 1 (vectorChecksum c)
    | none => 0

def runContains (_ : Unit) : IO Bool := do
  let A ← live fixedMatrix
  return Matrix.latticeContains A (Matrix.row A 0)

def runKernelBasis (_ : Unit) : IO UInt64 := do
  let A ← live fixedDeficientMatrix
  return checksum (Matrix.kernelBasis A)

def runCoeffsMiss (_ : Unit) : IO Bool := do
  let A ← live missMatrix
  let v ← live missVector
  return (Matrix.latticeCoeffs A v).isNone

def runContainsMiss (_ : Unit) : IO Bool := do
  let A ← live missMatrix
  let v ← live missVector
  return !(Matrix.latticeContains A v)

def runPivots (_ : Unit) : IO UInt64 := do
  let A ← live fixedMatrix
  return (Matrix.pivots A).foldl (fun acc x => mixHash acc (hash x)) 0

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
      (List.ofFn fun j : Fin input.cols =>
        input.entries.getD (i.val * input.cols + j.val) 0))

private def jsonMatrixChecksum (json : Lean.Json) : IO UInt64 := do
  let rows ← match json.getArr? with
    | .ok value => pure value
    | .error error => throw <| IO.userError s!"expected matrix rows: {error}"
  let mut acc : UInt64 := 0
  for rowJson in rows do
    let row ← match rowJson.getArr? with
      | .ok value => pure value
      | .error error => throw <| IO.userError s!"expected matrix row: {error}"
    for valueJson in row do
      let value ← match valueJson.getInt? with
        | .ok value => pure value
        | .error error => throw <| IO.userError s!"expected integer entry: {error}"
      acc := mixHash acc (hash value)
  return acc

private def runHexAt (input : Input) (_ : Unit) : IO UInt64 := do
  let ref ← IO.mkRef input
  let live ← ref.get
  return checksum (Matrix.hnf (matrix live))

private def runFlintAt (input : Input) (_ : Unit) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mat" "hnf"
    #[("rows", rowsJson input)]
  jsonMatrixChecksum result

private def runPariAt (input : Input) (_ : Unit) : IO UInt64 := do
  let result ← Hex.BenchOracle.Pari.runOp "fmpz_mat" "hnf"
    #[("rows", rowsJson input)]
  jsonMatrixChecksum result

def runHexDense16 : Unit → IO UInt64 := runHexAt (dense 16)
def runFlintDense16 : Unit → IO UInt64 := runFlintAt (dense 16)
def runPariDense16 : Unit → IO UInt64 := runPariAt (dense 16)
def runHexDense24 : Unit → IO UInt64 := runHexAt (dense 24)
def runFlintDense24 : Unit → IO UInt64 := runFlintAt (dense 24)
def runPariDense24 : Unit → IO UInt64 := runPariAt (dense 24)
def runHexDense32 : Unit → IO UInt64 := runHexAt (dense 32)
def runFlintDense32 : Unit → IO UInt64 := runFlintAt (dense 32)
def runPariDense32 : Unit → IO UInt64 := runPariAt (dense 32)
def runHexDense40 : Unit → IO UInt64 := runHexAt (dense 40)
def runFlintDense40 : Unit → IO UInt64 := runFlintAt (dense 40)
def runPariDense40 : Unit → IO UInt64 := runPariAt (dense 40)
def runHexDense48 : Unit → IO UInt64 := runHexAt (dense 48)
def runFlintDense48 : Unit → IO UInt64 := runFlintAt (dense 48)
def runPariDense48 : Unit → IO UInt64 := runPariAt (dense 48)
def runHexDeficient16 : Unit → IO UInt64 := runHexAt (deficient 16)
def runFlintDeficient16 : Unit → IO UInt64 := runFlintAt (deficient 16)
def runPariDeficient16 : Unit → IO UInt64 := runPariAt (deficient 16)
def runHexDeficient24 : Unit → IO UInt64 := runHexAt (deficient 24)
def runFlintDeficient24 : Unit → IO UInt64 := runFlintAt (deficient 24)
def runPariDeficient24 : Unit → IO UInt64 := runPariAt (deficient 24)
def runHexDeficient32 : Unit → IO UInt64 := runHexAt (deficient 32)
def runFlintDeficient32 : Unit → IO UInt64 := runFlintAt (deficient 32)
def runPariDeficient32 : Unit → IO UInt64 := runPariAt (deficient 32)
def runHexDeficient40 : Unit → IO UInt64 := runHexAt (deficient 40)
def runFlintDeficient40 : Unit → IO UInt64 := runFlintAt (deficient 40)
def runPariDeficient40 : Unit → IO UInt64 := runPariAt (deficient 40)
def runHexDeficient48 : Unit → IO UInt64 := runHexAt (deficient 48)
def runFlintDeficient48 : Unit → IO UInt64 := runFlintAt (deficient 48)
def runPariDeficient48 : Unit → IO UInt64 := runPariAt (deficient 48)
def runHexTall16 : Unit → IO UInt64 := runHexAt (tall 16)
def runFlintTall16 : Unit → IO UInt64 := runFlintAt (tall 16)
def runPariTall16 : Unit → IO UInt64 := runPariAt (tall 16)
def runHexTall24 : Unit → IO UInt64 := runHexAt (tall 24)
def runFlintTall24 : Unit → IO UInt64 := runFlintAt (tall 24)
def runPariTall24 : Unit → IO UInt64 := runPariAt (tall 24)
def runHexTall32 : Unit → IO UInt64 := runHexAt (tall 32)
def runFlintTall32 : Unit → IO UInt64 := runFlintAt (tall 32)
def runPariTall32 : Unit → IO UInt64 := runPariAt (tall 32)
def runHexTall40 : Unit → IO UInt64 := runHexAt (tall 40)
def runFlintTall40 : Unit → IO UInt64 := runFlintAt (tall 40)
def runPariTall40 : Unit → IO UInt64 := runPariAt (tall 40)
def runHexTall48 : Unit → IO UInt64 := runHexAt (tall 48)
def runFlintTall48 : Unit → IO UInt64 := runFlintAt (tall 48)
def runPariTall48 : Unit → IO UInt64 := runPariAt (tall 48)
def runHexConjugate16 : Unit → IO UInt64 := runHexAt (conjugate 16)
def runFlintConjugate16 : Unit → IO UInt64 := runFlintAt (conjugate 16)
def runPariConjugate16 : Unit → IO UInt64 := runPariAt (conjugate 16)
def runHexConjugate24 : Unit → IO UInt64 := runHexAt (conjugate 24)
def runFlintConjugate24 : Unit → IO UInt64 := runFlintAt (conjugate 24)
def runPariConjugate24 : Unit → IO UInt64 := runPariAt (conjugate 24)
def runHexConjugate32 : Unit → IO UInt64 := runHexAt (conjugate 32)
def runFlintConjugate32 : Unit → IO UInt64 := runFlintAt (conjugate 32)
def runPariConjugate32 : Unit → IO UInt64 := runPariAt (conjugate 32)
def runHexConjugate40 : Unit → IO UInt64 := runHexAt (conjugate 40)
def runFlintConjugate40 : Unit → IO UInt64 := runFlintAt (conjugate 40)
def runPariConjugate40 : Unit → IO UInt64 := runPariAt (conjugate 40)
def runHexConjugate48 : Unit → IO UInt64 := runHexAt (conjugate 48)
def runFlintConjugate48 : Unit → IO UInt64 := runFlintAt (conjugate 48)
def runPariConjugate48 : Unit → IO UInt64 := runPariAt (conjugate 48)

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

/- Cost-model derivation: fixed-aspect rank profiling plus the nonzero
principal reductions make cubic matrix-entry visits. Their Euclidean pivot
work grows with the logarithmic controlled-family operand ladder, yielding the
registered `O(n³ log n)` wall model; unrestricted scheduling remains `O(n⁴)`. -/
setup_benchmark runDense n => n ^ 3 * Nat.log2 (n + 1) with prep := dense where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}
/- Cost-model derivation: active rank is `n / 2`, leaving cubic entry visits;
the dependent rows multiply bounded generators by indices through `n`, so
Euclidean operand work contributes the explicit `log n` factor. -/
setup_benchmark runDeficient n => n ^ 3 * Nat.log2 (n + 1) with prep := deficient where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}
/- Cost-model derivation: the tall family has `4n` rows and `n` columns, so
the constant aspect ratio does not change the cubic controlled-family model;
redundant signed rows exercise reconstruction without increasing rank. -/
setup_benchmark runTall n => n ^ 3 with prep := tall where {
  paramFloor := 8, paramCeiling := 64,
  paramSchedule := .custom #[8, 12, 16, 24, 32, 48, 64]
  verdictWarmupFraction := 0.3
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}
/- Cost-model derivation: the dense unit-triangular factors give a known
full-rank diagonal form while increasing coefficient width with dimension.
Cubic matrix-entry visits plus the measured controlled operand factor give
the registered `O(n³ log n)` wall model. -/
setup_benchmark runConjugate n => n ^ 3 * Nat.log2 (n + 1) with prep := conjugate where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: fraction-free profiling visits a cubic number of
matrix entries. Dense minors grow linearly in bit width on this bounded-entry
family, giving the registered controlled-family `O(n³ log n)` wall model. -/
setup_benchmark runProfile n => n ^ 3 * Nat.log2 (n + 1) with prep := dense where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: rank-profile preparation is excluded from this
target. The principal phase admits `n` rows, restores at most `n` earlier
pivots per row, and each row update visits `n` entries. Its controlled dense
operand ladder contributes the same logarithmic factor as the complete route. -/
setup_benchmark runPrincipalDense n => n ^ 3 * Nat.log2 (n + 1)
    with prep := principalInput where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: rank projects one value from the same dense
form-only run, so its controlled wall model is the `O(n³ log n)` form model. -/
setup_benchmark runRankDense n => n ^ 3 * Nat.log2 (n + 1) with prep := dense where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: basis extraction shares one form-only result across
its rank and quadratic row slice, preserving the dense `O(n³ log n)`
controlled wall model. -/
setup_benchmark runBasisDense n => n ^ 3 * Nat.log2 (n + 1) with prep := dense where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: transform accumulation follows the same dense pivot
schedule and updates an additional fixed-aspect matrix. On this controlled
family it preserves the `O(n³ log n)` wall model; the SPEC retains the larger
unrestricted scheduled-update ceiling. -/
setup_benchmark runDataDense n => n ^ 3 * Nat.log2 (n + 1) with prep := dense where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: inverse accumulation adds another fixed-aspect row
update to the transform schedule, preserving its controlled `O(n³ log n)` wall
model while increasing the constant. -/
setup_benchmark runWithInvDense n => n ^ 3 * Nat.log2 (n + 1) with prep := dense where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: constructive membership is `hnfData` plus quadratic
solve and residual work, so the dense controlled wall model remains
`O(n³ log n)`. -/
setup_benchmark runCoeffsDense n => n ^ 3 * Nat.log2 (n + 1) with prep := dense where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: membership projects `Option.isSome` from the same
constructive solve, preserving its dense `O(n³ log n)` controlled wall model. -/
setup_benchmark runContainsDense n => n ^ 3 * Nat.log2 (n + 1) with prep := dense where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: kernel extraction shares one transform-producing run
across its rank and quadratic row slice. The controlled deficient-family wall
model is therefore `O(n³ log n)`. -/
setup_benchmark runKernelDeficient n => n ^ 3 * Nat.log2 (n + 1)
    with prep := deficient where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: pivot extraction adds a linear scan to one form-only
run, preserving the dense `O(n³ log n)` controlled wall model. -/
setup_benchmark runPivotsDense n => n ^ 3 * Nat.log2 (n + 1) with prep := dense where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: the lattice index adds a linear pivot product to one
form-only run, preserving the dense `O(n³ log n)` controlled wall model. -/
setup_benchmark runIndexDense n => n ^ 3 * Nat.log2 (n + 1) with prep := dense where {
  paramFloor := 16, paramCeiling := 128,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: the entry-level HNF predicate has quadratically many
clauses. Single entries use constant-time flat access and the zero-row clauses
scan at most `n` complete rows, giving a quadratic prepared-certificate model. -/
setup_benchmark runShapePrepared n => n ^ 2 with prep := shapeInput where {
  paramFloor := 16, paramCeiling := 256,
  paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
  maxSecondsPerCall := 10.0
}

/- Cost-model derivation: certificate replay performs two packed product
checks with `n²` big-by-small terms and a quadratic shape scan. The packed
word width grows across the ladder, contributing the measured logarithmic
factor on this bounded certificate family. -/
setup_benchmark runCertPrepared n => n ^ 2 * Nat.log2 (n + 1) with prep := certInput where {
  paramFloor := 64, paramCeiling := 512,
  paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
  targetInnerNanos := 2_000_000_000, outerTrials := 3
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

private def apiExpected (expected : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { apiConfig with expectedHash := some expected }

private def hexExpected (expected : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { hexComparisonConfig with expectedHash := some expected }

private def externalExpected (expected : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { externalComparisonConfig with expectedHash := some expected }

setup_fixed_benchmark runIsHNFForm where apiExpected 0xb
setup_fixed_benchmark runRank where apiExpected 0x8
setup_fixed_benchmark runBasis where apiExpected 0x4bd6c0414a37c54a
setup_fixed_benchmark runData where apiExpected 0xd37fb7926b798a32
setup_fixed_benchmark runWithInv where apiExpected 0x91815657fb9e95e2
setup_fixed_benchmark runCoeffs where apiExpected 0x93d3a019b62bba94
setup_fixed_benchmark runContains where apiExpected 0xb
setup_fixed_benchmark runKernelBasis where apiExpected 0x781397e5d22ca373
setup_fixed_benchmark runCoeffsMiss where apiExpected 0xb
setup_fixed_benchmark runContainsMiss where apiExpected 0xb
setup_fixed_benchmark runPivots where apiExpected 0x88b839d5137f8c3d
setup_fixed_benchmark runIndex where apiExpected 0x52738
setup_fixed_benchmark runCert where apiExpected 0xb

setup_fixed_benchmark runFlintOverhead where externalExpected 0x0
setup_fixed_benchmark runPariOverhead where externalExpected 0x0
setup_fixed_benchmark runHexDense16 where hexExpected 0xd4c4d30cf11e3902
setup_fixed_benchmark runFlintDense16 where externalExpected 0xd4c4d30cf11e3902
setup_fixed_benchmark runPariDense16 where externalExpected 0xd4c4d30cf11e3902
setup_fixed_benchmark runHexDense24 where hexExpected 0xc2db6d9cd48562cf
setup_fixed_benchmark runFlintDense24 where externalExpected 0xc2db6d9cd48562cf
setup_fixed_benchmark runPariDense24 where externalExpected 0xc2db6d9cd48562cf
setup_fixed_benchmark runHexDense32 where hexExpected 0x7dea452eb86f21c4
setup_fixed_benchmark runFlintDense32 where externalExpected 0x7dea452eb86f21c4
setup_fixed_benchmark runPariDense32 where externalExpected 0x7dea452eb86f21c4
setup_fixed_benchmark runHexDense40 where hexExpected 0x3e6a06331c9a70f5
setup_fixed_benchmark runFlintDense40 where externalExpected 0x3e6a06331c9a70f5
setup_fixed_benchmark runPariDense40 where externalExpected 0x3e6a06331c9a70f5
setup_fixed_benchmark runHexDense48 where hexExpected 0xf0b970d34f3479cf
setup_fixed_benchmark runFlintDense48 where externalExpected 0xf0b970d34f3479cf
setup_fixed_benchmark runPariDense48 where externalExpected 0xf0b970d34f3479cf
setup_fixed_benchmark runHexDeficient16 where hexExpected 0x8c3b42aee1b184e
setup_fixed_benchmark runFlintDeficient16 where externalExpected 0x8c3b42aee1b184e
setup_fixed_benchmark runPariDeficient16 where externalExpected 0x8c3b42aee1b184e
setup_fixed_benchmark runHexDeficient24 where hexExpected 0x9a533e7da7244459
setup_fixed_benchmark runFlintDeficient24 where externalExpected 0x9a533e7da7244459
setup_fixed_benchmark runPariDeficient24 where externalExpected 0x9a533e7da7244459
setup_fixed_benchmark runHexDeficient32 where hexExpected 0xe5df8cb1544b5979
setup_fixed_benchmark runFlintDeficient32 where externalExpected 0xe5df8cb1544b5979
setup_fixed_benchmark runPariDeficient32 where externalExpected 0xe5df8cb1544b5979
setup_fixed_benchmark runHexDeficient40 where hexExpected 0x705d86c1ef31d9c9
setup_fixed_benchmark runFlintDeficient40 where externalExpected 0x705d86c1ef31d9c9
setup_fixed_benchmark runPariDeficient40 where externalExpected 0x705d86c1ef31d9c9
setup_fixed_benchmark runHexDeficient48 where hexExpected 0x98d873e64dfda3bc
setup_fixed_benchmark runFlintDeficient48 where externalExpected 0x98d873e64dfda3bc
setup_fixed_benchmark runPariDeficient48 where externalExpected 0x98d873e64dfda3bc
setup_fixed_benchmark runHexTall16 where hexExpected 0x8194afcd561bfd53
setup_fixed_benchmark runFlintTall16 where externalExpected 0x8194afcd561bfd53
setup_fixed_benchmark runPariTall16 where externalExpected 0x8194afcd561bfd53
setup_fixed_benchmark runHexTall24 where hexExpected 0x720fca5c6fa3aec1
setup_fixed_benchmark runFlintTall24 where externalExpected 0x720fca5c6fa3aec1
setup_fixed_benchmark runPariTall24 where externalExpected 0x720fca5c6fa3aec1
setup_fixed_benchmark runHexTall32 where hexExpected 0x418e1a4c9e9d84b3
setup_fixed_benchmark runFlintTall32 where externalExpected 0x418e1a4c9e9d84b3
setup_fixed_benchmark runPariTall32 where externalExpected 0x418e1a4c9e9d84b3
setup_fixed_benchmark runHexTall40 where hexExpected 0x39dab28adc1593b5
setup_fixed_benchmark runFlintTall40 where externalExpected 0x39dab28adc1593b5
setup_fixed_benchmark runPariTall40 where externalExpected 0x39dab28adc1593b5
setup_fixed_benchmark runHexTall48 where hexExpected 0xb51a4d975bdc6feb
setup_fixed_benchmark runFlintTall48 where externalExpected 0xb51a4d975bdc6feb
setup_fixed_benchmark runPariTall48 where externalExpected 0xb51a4d975bdc6feb
setup_fixed_benchmark runHexConjugate16 where hexExpected 0x1b4006b1f4d4df66
setup_fixed_benchmark runFlintConjugate16 where externalExpected 0x1b4006b1f4d4df66
setup_fixed_benchmark runPariConjugate16 where externalExpected 0x1b4006b1f4d4df66
setup_fixed_benchmark runHexConjugate24 where hexExpected 0xe47f13aca06b7628
setup_fixed_benchmark runFlintConjugate24 where externalExpected 0xe47f13aca06b7628
setup_fixed_benchmark runPariConjugate24 where externalExpected 0xe47f13aca06b7628
setup_fixed_benchmark runHexConjugate32 where hexExpected 0x531c1c24c585ac12
setup_fixed_benchmark runFlintConjugate32 where externalExpected 0x531c1c24c585ac12
setup_fixed_benchmark runPariConjugate32 where externalExpected 0x531c1c24c585ac12
setup_fixed_benchmark runHexConjugate40 where hexExpected 0xfc1deb59344974c8
setup_fixed_benchmark runFlintConjugate40 where externalExpected 0xfc1deb59344974c8
setup_fixed_benchmark runPariConjugate40 where externalExpected 0xfc1deb59344974c8
setup_fixed_benchmark runHexConjugate48 where hexExpected 0x501203bf9b14db75
setup_fixed_benchmark runFlintConjugate48 where externalExpected 0x501203bf9b14db75
setup_fixed_benchmark runPariConjugate48 where externalExpected 0x501203bf9b14db75

end Hex.HermiteBench

private def growthInput (family : String) (n : Nat) : IO Hex.HermiteBench.Input :=
  match family with
  | "dense" => pure <| Hex.HermiteBench.dense n
  | "deficient" => pure <| Hex.HermiteBench.deficient n
  | "tall" => pure <| Hex.HermiteBench.tall n
  | "conjugate" => pure <| Hex.HermiteBench.conjugate n
  | _ => throw <| IO.userError s!"unknown growth family: {family}"

private def growthMain (family : String) (args : List String) : IO UInt32 := do
  for arg in args do
    let some n := arg.toNat?
      | throw <| IO.userError s!"invalid growth dimension: {arg}"
    let input ← growthInput family n
    let (peak, output, agrees) := Hex.HermiteBench.growthData input
    unless agrees do
      throw <| IO.userError s!"instrumented result mismatch: family={family} n={n}"
    IO.println s!"family={family} n={n} peakBits={peak} outputBits={output}"
  return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | "growth" :: family :: dimensions => growthMain family dimensions
  | _ => LeanBench.Cli.dispatch args
