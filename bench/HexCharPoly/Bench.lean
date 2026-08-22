/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexCharPoly
import Hex.BenchOracle.Flint
import Hex.BenchOracle.Pari
import LeanBench

/-!
Benchmark registrations for Samuelson--Berkowitz characteristic polynomials.

The headline random family has separate dimension and entry-bit-width ladders.
Its return value records the peak bit size among every Berkowitz Toeplitz
column and every intermediate coefficient vector.  The structured family
checks companion matrices and Jordan blocks against closed-form answers inside
the benchmark.  FLINT and PARI are fixed-rung informational comparators; PARI
uses flag `3`, its division-free Berkowitz implementation.
-/

namespace Hex.CharPolyBench

/-- A dynamically sized square integer matrix prepared outside the timed call. -/
structure Input where
  n : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

private def matrixOfInput (input : Input) : Hex.Matrix Int input.n input.n :=
  Hex.Matrix.ofFn fun i j => input.entries.getD (i.val * input.n + j.val) 0

private def nextSeed (seed : UInt64) : UInt64 :=
  seed * 6364136223846793005 + 1442695040888963407

private structure Generator where
  seed : UInt64
  entries : Array Int

/-- Deterministic dense mixed-sign entries bounded by the requested bit width. -/
def randomInput (n bits : Nat) : Input :=
  let modulus := 2 ^ (min bits 62)
  let state := (Array.range (n * n)).foldl (fun state _ =>
    let seed := nextSeed state.seed
    let magnitude := seed.toNat % modulus
    let value := if seed &&& 1 = 0 then Int.ofNat magnitude else -Int.ofNat magnitude
    { seed := seed, entries := state.entries.push value })
    ({ seed := 0xC0FFEE, entries := #[] } : Generator)
  { n, entries := state.entries }

def prepRandomDimension (n : Nat) : Input := randomInput n 12
def prepRandomBits (bits : Nat) : Input := randomInput 10 bits

/-- Deterministic tridiagonal entries in `{-1, 0, 1, 2}`. -/
def prepSmallEntry (n : Nat) : Input :=
  { n
    entries := (Array.range (n * n)).map fun index =>
      let row := index / n
      let column := index % n
      if row = column then 2
      else if row + 1 = column then -1
      else if column + 1 = row then 1
      else 0 }

private def bitSize (value : Int) : Nat :=
  if value = 0 then 0 else Nat.log2 value.natAbs + 1

private def peakVector {n : Nat} (values : Vector Int n) : Nat :=
  values.toArray.foldl (fun peak value => max peak (bitSize value)) 0

private structure GrowthResult (n : Nat) where
  coefficients : Vector Int (n + 1)
  peakBits : Nat

private def berkowitzGrowth (A : Hex.Matrix Int n n) :
    (k : Nat) → k ≤ n → GrowthResult k
  | 0, _ => { coefficients := #v[1], peakBits := 1 }
  | k + 1, hk =>
      let prior := berkowitzGrowth A k (by omega)
      let column := Hex.Matrix.berkowitzColumn A k hk
      let coefficients := Hex.Matrix.berkowitzStep A k hk prior.coefficients
      { coefficients
        peakBits := max prior.peakBits (max (peakVector column) (peakVector coefficients)) }

/-- Timed Berkowitz computation with coefficient-growth observation. -/
def runRandomDense (input : Input) : UInt64 × Nat :=
  let matrix := matrixOfInput input
  let result := berkowitzGrowth matrix input.n (Nat.le_refl input.n)
  (hash result.coefficients.reverse.toArray, result.peakBits)

/-- Timed public characteristic polynomial on the small-entry tridiagonal family. -/
def runSmallEntry (input : Input) : UInt64 :=
  hash (Hex.Matrix.charPoly (matrixOfInput input)).toArray

private def mulLinear (a : Array Int) (root : Int) : Array Int :=
  (Array.range (a.size + 1)).map fun i =>
    -root * a.getD i 0 + if i = 0 then 0 else a.getD (i - 1) 0

private def jordanCoefficients (n : Nat) (eigenvalue : Int) : Array Int :=
  (List.range n).foldl (fun coefficients _ => mulLinear coefficients eigenvalue) #[1]

private def companionCoefficients (n : Nat) : Array Int :=
  (Array.range (n + 1)).map fun i => if i = n then 1 else Int.ofNat (i + 1) * (-1) ^ i

private def companionInput (n : Nat) : Input :=
  let coefficients := companionCoefficients n
  { n
    entries := (Array.range (n * n)).map fun index =>
      let row := index / n
      let column := index % n
      if column + 1 = n then -coefficients.getD row 0
      else if row = column + 1 then 1
      else 0 }

private def jordanInput (n : Nat) (eigenvalue : Int) : Input :=
  { n
    entries := (Array.range (n * n)).map fun index =>
      let row := index / n
      let column := index % n
      if row = column then eigenvalue
      else if row + 1 = column then 1
      else 0 }

/-- Companion and Jordan cases, each checked against its closed form. -/
def runStructured (n : Nat) : UInt64 :=
  let companion := Hex.Matrix.charPoly (matrixOfInput (companionInput n))
  let jordan := Hex.Matrix.charPoly (matrixOfInput (jordanInput n 3))
  let companionExpected := companionCoefficients n
  let jordanExpected := jordanCoefficients n 3
  if companion.toArray = companionExpected ∧ jordan.toArray = jordanExpected then
    mixHash (hash companion.toArray) (hash jordan.toArray)
  else
    panic! "structured characteristic-polynomial self-check failed"

-- Cost model: summing the cubic matrix-vector work over `n` Berkowitz stages
-- gives the algorithm's `O(n^4)` ring-operation bound.
setup_benchmark runRandomDense n => n * n * n * n
  with prep := prepRandomDimension
  where {
    paramFloor := 4
    paramCeiling := 16
    paramSchedule := .custom #[4, 6, 8, 10, 12, 14, 16]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 300000000
    slopeTolerance := 0.35
  }

def runRandomBitWidth (bits : Nat) : UInt64 × Nat :=
  runRandomDense (prepRandomBits bits)

-- Cost model: dimension is fixed at ten, while the input operand width grows
-- linearly with `bits`; `bits + 1` also keeps the model nonzero at the origin.
setup_benchmark runRandomBitWidth bits => bits + 1
  where {
    paramFloor := 4
    paramCeiling := 48
    paramSchedule := .custom #[4, 8, 12, 16, 24, 32, 40, 48]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 300000000
    slopeTolerance := 0.5
  }

-- Cost model: fixed small entries moderate operand growth, leaving the
-- Samuelson--Berkowitz `O(n^4)` ring-operation count as the declared model.
setup_benchmark runSmallEntry n => n * n * n * n
  with prep := prepSmallEntry
  where {
    paramFloor := 4
    paramCeiling := 20
    paramSchedule := .custom #[4, 6, 8, 10, 12, 16, 20]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 300000000
    slopeTolerance := 0.35
  }

-- Cost model: companion and Jordan structure changes the values but not the
-- dense Berkowitz recurrence, whose worst-case operation count is `O(n^4)`.
setup_benchmark runStructured n => n * n * n * n
  where {
    paramFloor := 4
    paramCeiling := 16
    paramSchedule := .custom #[4, 6, 8, 10, 12, 14, 16]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 300000000
    slopeTolerance := 0.35
  }

private def rowsJson (input : Input) : Lean.Json :=
  Lean.Json.arr (Array.ofFn fun i : Fin input.n =>
    Hex.BenchOracle.Flint.intsToJson
      (List.ofFn fun j : Fin input.n => input.entries.getD (i.val * input.n + j.val) 0))

private def comparatorInput (n : Nat) : Input := prepRandomDimension n

private def runHexAt (n : Nat) (_ : Unit) : IO (List Int) :=
  return (Hex.Matrix.charPoly (matrixOfInput (comparatorInput n))).toArray.toList

private def runFlintAt (n : Nat) (_ : Unit) : IO (List Int) := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mat" "charpoly"
    #[("rows", rowsJson (comparatorInput n))]
  Hex.BenchOracle.Flint.jsonToInts result

private def runPariAt (n : Nat) (_ : Unit) : IO (List Int) := do
  let result ← Hex.BenchOracle.Pari.runOp "fmpz_mat" "charpoly_berkowitz"
    #[("rows", rowsJson (comparatorInput n))]
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

private def hexComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := 8.0

private def externalComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := 8.0
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

end Hex.CharPolyBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
