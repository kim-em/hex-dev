/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexCharPoly
import HexCharPoly.Carriers
import Hex.BenchOracle.Flint
import Hex.BenchOracle.Pari
import LeanBench

/-!
Benchmark registrations for Samuelson--Berkowitz characteristic polynomials.

The headline random family has separate dimension and entry-bit-width ladders.
The `growth` command times the public computation and separately observes the
peak bit size among every Berkowitz Toeplitz column and every intermediate
coefficient vector, reporting both measurements for both ladders as JSONL.
The structured family checks companion matrices and Jordan blocks against
closed-form answers inside the benchmark.  FLINT and PARI are fixed-rung
informational comparators; PARI uses flag `3`, its division-free Berkowitz
implementation.
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

private def randomDimensionSchedule : Array Nat := #[4, 6, 8, 10, 12, 14, 16]
private def randomBitSchedule : Array Nat := #[4, 8, 12, 16, 24, 32, 40, 48]

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
      let coefficients := Hex.Matrix.toeplitzMulVec column prior.coefficients
      { coefficients
        peakBits := max prior.peakBits (max (peakVector column) (peakVector coefficients)) }

/-- Timed public characteristic-polynomial computation for random input. -/
def runRandomDense (input : Input) : UInt64 :=
  hash (Hex.Matrix.charPoly (matrixOfInput input)).toArray

private def randomGrowth (input : Input) : UInt64 × Nat :=
  let matrix := matrixOfInput input
  let result := berkowitzGrowth matrix input.n (Nat.le_refl input.n)
  (hash result.coefficients.reverse.toArray, result.peakBits)

private def natJson (value : Nat) : Lean.Json :=
  Lean.Json.num (Lean.JsonNumber.fromNat value)

/-- Time the public computation, independently instrument the same input, and
emit both observations as one JSONL record.  The checksum equality makes the
instrumented recurrence accountable to the public result without charging its
extra peak-bit folds to the wallclock measurement. -/
private def emitGrowth (axis : String) (parameter dimension bits : Nat)
    (input : Input) : IO Unit := do
  let start ← IO.monoNanosNow
  let checksum := runRandomDense input
  LeanBench.blackBox checksum
  let stop ← IO.monoNanosNow
  let growth := randomGrowth input
  LeanBench.blackBox (hash growth)
  if growth.1 != checksum then
    throw <| IO.userError "growth instrumentation disagrees with public charPoly"
  IO.println <| (Lean.Json.mkObj [
    ("family", Lean.Json.str "random-dense-charpoly"),
    ("axis", Lean.Json.str axis),
    ("parameter", natJson parameter),
    ("dimension", natJson dimension),
    ("entry_bits", natJson bits),
    ("elapsed_nanos", natJson (stop - start)),
    ("peak_bits", natJson growth.2),
    ("checksum", natJson checksum.toNat)]).compress

/-- Emit measured intermediate-growth rows for the random dimension and
entry-bit-width ladders. -/
def growthReport : IO UInt32 := do
  for n in randomDimensionSchedule do
    emitGrowth "dimension" n n 12 (prepRandomDimension n)
  for bits in randomBitSchedule do
    emitGrowth "entry-bits" bits 10 bits (prepRandomBits bits)
  return 0

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
    paramSchedule := .custom randomDimensionSchedule
    maxSecondsPerCall := 5.0
    targetInnerNanos := 300000000
    slopeTolerance := 0.35
  }

def runRandomBitWidth (bits : Nat) : UInt64 :=
  runRandomDense (prepRandomBits bits)

-- Cost model: dimension is fixed at ten, while the input operand width grows
-- linearly with `bits`; `bits + 1` also keeps the model nonzero at the origin.
setup_benchmark runRandomBitWidth bits => bits + 1
  where {
    paramFloor := 4
    paramCeiling := 48
    paramSchedule := .custom randomBitSchedule
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

/-! Carrier comparisons require SymPy in `HEX_CARRIER_BENCH_PYTHON` (default
python3). External registrations are scheduled-only; `verify-ci` excludes them.
Each fixed rung observes every canonical Toeplitz/coeff-vector entry and hashes
the entire canonical polynomial. Timings include structural instrumentation. -/
namespace Hex.CharPolyBench
open Hex CharPolyCarriers Lean
open scoped Hex.CharPolyCarriers

private def peak [Lean.Grind.CommRing R] (size : R → Nat)
    (A : Matrix R n n) : (k : Nat) → k ≤ n → Vector R (k + 1) × Nat
  | 0, _ => (#v[1], size 1)
  | k + 1, hk =>
    let (prior, oldPeak) := peak size A k (by omega)
    let column := Matrix.berkowitzColumn A k hk
    let coeffs := Matrix.toeplitzMulVec column prior
    let columnPeak := column.toArray.foldl (fun a c => max a (size c)) oldPeak
    (coeffs, coeffs.toArray.foldl (fun a c => max a (size c)) columnPeak)

private def denseSize [Zero R] [DecidableEq R] (p : DensePoly R) : Nat := p.size
private def mvSize [Zero R] (p : MV n R) : Nat := p.termCount
private def fractionSize (f : RationalFn Rat) : Nat := f.num.size + f.den.size

private def runCarrier [Lean.Grind.CommRing R] [DecidableEq R]
    (encode : R → Json) (size : R → Nat) (n : Nat) (entry : Nat → Nat → R) : IO String := do
  let (coeffs, maximum) := peak size (matrix entry "dense" n) n (Nat.le_refl n)
  LeanBench.blackBox (hash maximum)
  return (Json.arr (coeffs.reverse.toArray.map encode)).compress

def runCharDenseInt (n degree : Nat) (_ : Unit) : IO String :=
  runCarrier (denseJson intJson) denseSize n (denseEntry id degree)
def runCharDenseRat (n degree : Nat) (_ : Unit) : IO String :=
  runCarrier (denseJson ratJson) denseSize n (denseEntry ratScalar degree)
def runCharDenseMod (n degree : Nat) (_ : Unit) : IO String :=
  runCarrier (denseJson modJson) denseSize n (denseEntry (fun z => (z : Mod)) degree)
def runCharMvInt (n terms : Nat) (_ : Unit) : IO String :=
  runCarrier (mvJson intJson) mvSize n (mvEntry id 3 terms)
def runCharMvRat (n terms : Nat) (_ : Unit) : IO String :=
  runCarrier (mvJson ratJson) mvSize n (mvEntry ratScalar 3 terms)
def runCharRatFn (n degree : Nat) (_ : Unit) : IO String :=
  runCarrier fractionJson fractionSize n (ratFnEntry degree)

initialize carrierDriver : IO.Ref (Option Hex.BenchOracle.Flint.PersistentComparator) ← IO.mkRef none

private def resolveCarrier : IO Hex.BenchOracle.Flint.PersistentComparator := do
  if let some child ← carrierDriver.get then return child
  let python := (← IO.getEnv "HEX_CARRIER_BENCH_PYTHON").getD "python3"
  let driver ← match ← IO.getEnv "HEX_CARRIER_BENCH_DRIVER" with
    | some path => pure path
    | none => do
      let path : System.FilePath := "scripts/oracle/matrix_carriers.py"
      pure (if ← path.pathExists then path.toString else "../scripts/oracle/matrix_carriers.py")
  let child ← Hex.BenchOracle.Flint.PersistentComparator.spawn python #[driver, "--serve"]
  carrierDriver.set (some child)
  return child

private def sympyRequest (request : Json) : IO String := do
  let requestLine := request.compress
  let line ← try
      (← resolveCarrier).requestLine requestLine
    catch _ => do
      carrierDriver.set none
      try (← resolveCarrier).requestLine requestLine
      catch _ => throw (IO.userError "carrier comparator transport failed after restarting its driver")
  let reply ← IO.ofExcept (Json.parse line)
  if (reply.getObjValAs? Bool "ok").toOption != some true then
    throw (IO.userError s!"carrier oracle failed: {line}")
  return (← IO.ofExcept (reply.getObjVal? "result")).compress

private def runSympy [Lean.Grind.CommRing R] [DecidableEq R]
    (encode : R → Json) (carrier : String) (arity n : Nat) (entry : Nat → Nat → R) : IO String :=
  sympyRequest (request encode carrier "dense" arity (matrix entry "dense" n))

def sympyDenseInt (n degree : Nat) (_ : Unit) : IO String :=
  runSympy (denseJson intJson) "dense_int" 1 n (denseEntry id degree)
def sympyDenseRat (n degree : Nat) (_ : Unit) : IO String :=
  runSympy (denseJson ratJson) "dense_rat" 1 n (denseEntry ratScalar degree)
def sympyDenseMod (n degree : Nat) (_ : Unit) : IO String :=
  runSympy (denseJson modJson) "dense_mod" 1 n (denseEntry (fun z => (z : Mod)) degree)
def sympyMvInt (n terms : Nat) (_ : Unit) : IO String :=
  runSympy (mvJson intJson) "mv_int" 3 n (mvEntry id 3 terms)
def sympyMvRat (n terms : Nat) (_ : Unit) : IO String :=
  runSympy (mvJson ratJson) "mv_rat" 3 n (mvEntry ratScalar 3 terms)
def sympyRatFn (n degree : Nat) (_ : Unit) : IO String :=
  runSympy fractionJson "rat_fn" 1 n (ratFnEntry degree)

def carrierNoop (_ : Unit) : IO String :=
  sympyRequest (Json.mkObj [("op", toJson "noop")])

private def carrierConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := 30
  warmupFirstIter := true
  tags := #["carrier", "hex"]
private def sympyConfig : LeanBench.FixedBenchmarkConfig :=
  { carrierConfig with tags := #["carrier", "scheduled-only"] }

setup_fixed_benchmark carrierNoop where sympyConfig

-- Fixed latency sweeps make no fitted complexity claim: entry degree/term
-- growth changes coefficient cost independently of Berkowitz's O(n^4) count.
-- Multivariate rungs keep arity three and total degree five fixed.

def DenseInt.n2k1 : Unit → IO String := runCharDenseInt 2 1
def SympyDenseInt.n2k1 : Unit → IO String := sympyDenseInt 2 1
setup_fixed_benchmark DenseInt.n2k1 where carrierConfig
setup_fixed_benchmark SympyDenseInt.n2k1 where sympyConfig

def DenseInt.n3k1 : Unit → IO String := runCharDenseInt 3 1
def SympyDenseInt.n3k1 : Unit → IO String := sympyDenseInt 3 1
setup_fixed_benchmark DenseInt.n3k1 where carrierConfig
setup_fixed_benchmark SympyDenseInt.n3k1 where sympyConfig

def DenseInt.n4k1 : Unit → IO String := runCharDenseInt 4 1
def SympyDenseInt.n4k1 : Unit → IO String := sympyDenseInt 4 1
setup_fixed_benchmark DenseInt.n4k1 where carrierConfig
setup_fixed_benchmark SympyDenseInt.n4k1 where sympyConfig

def DenseInt.n3k2 : Unit → IO String := runCharDenseInt 3 2
def SympyDenseInt.n3k2 : Unit → IO String := sympyDenseInt 3 2
setup_fixed_benchmark DenseInt.n3k2 where carrierConfig
setup_fixed_benchmark SympyDenseInt.n3k2 where sympyConfig

def DenseInt.n3k3 : Unit → IO String := runCharDenseInt 3 3
def SympyDenseInt.n3k3 : Unit → IO String := sympyDenseInt 3 3
setup_fixed_benchmark DenseInt.n3k3 where carrierConfig
setup_fixed_benchmark SympyDenseInt.n3k3 where sympyConfig

def DenseRat.n2k1 : Unit → IO String := runCharDenseRat 2 1
def SympyDenseRat.n2k1 : Unit → IO String := sympyDenseRat 2 1
setup_fixed_benchmark DenseRat.n2k1 where carrierConfig
setup_fixed_benchmark SympyDenseRat.n2k1 where sympyConfig

def DenseRat.n3k1 : Unit → IO String := runCharDenseRat 3 1
def SympyDenseRat.n3k1 : Unit → IO String := sympyDenseRat 3 1
setup_fixed_benchmark DenseRat.n3k1 where carrierConfig
setup_fixed_benchmark SympyDenseRat.n3k1 where sympyConfig

def DenseRat.n4k1 : Unit → IO String := runCharDenseRat 4 1
def SympyDenseRat.n4k1 : Unit → IO String := sympyDenseRat 4 1
setup_fixed_benchmark DenseRat.n4k1 where carrierConfig
setup_fixed_benchmark SympyDenseRat.n4k1 where sympyConfig

def DenseRat.n3k2 : Unit → IO String := runCharDenseRat 3 2
def SympyDenseRat.n3k2 : Unit → IO String := sympyDenseRat 3 2
setup_fixed_benchmark DenseRat.n3k2 where carrierConfig
setup_fixed_benchmark SympyDenseRat.n3k2 where sympyConfig

def DenseRat.n3k3 : Unit → IO String := runCharDenseRat 3 3
def SympyDenseRat.n3k3 : Unit → IO String := sympyDenseRat 3 3
setup_fixed_benchmark DenseRat.n3k3 where carrierConfig
setup_fixed_benchmark SympyDenseRat.n3k3 where sympyConfig

def DenseMod.n2k1 : Unit → IO String := runCharDenseMod 2 1
def SympyDenseMod.n2k1 : Unit → IO String := sympyDenseMod 2 1
setup_fixed_benchmark DenseMod.n2k1 where carrierConfig
setup_fixed_benchmark SympyDenseMod.n2k1 where sympyConfig

def DenseMod.n3k1 : Unit → IO String := runCharDenseMod 3 1
def SympyDenseMod.n3k1 : Unit → IO String := sympyDenseMod 3 1
setup_fixed_benchmark DenseMod.n3k1 where carrierConfig
setup_fixed_benchmark SympyDenseMod.n3k1 where sympyConfig

def DenseMod.n4k1 : Unit → IO String := runCharDenseMod 4 1
def SympyDenseMod.n4k1 : Unit → IO String := sympyDenseMod 4 1
setup_fixed_benchmark DenseMod.n4k1 where carrierConfig
setup_fixed_benchmark SympyDenseMod.n4k1 where sympyConfig

def DenseMod.n3k2 : Unit → IO String := runCharDenseMod 3 2
def SympyDenseMod.n3k2 : Unit → IO String := sympyDenseMod 3 2
setup_fixed_benchmark DenseMod.n3k2 where carrierConfig
setup_fixed_benchmark SympyDenseMod.n3k2 where sympyConfig

def DenseMod.n3k3 : Unit → IO String := runCharDenseMod 3 3
def SympyDenseMod.n3k3 : Unit → IO String := sympyDenseMod 3 3
setup_fixed_benchmark DenseMod.n3k3 where carrierConfig
setup_fixed_benchmark SympyDenseMod.n3k3 where sympyConfig

def MvInt.n2k2 : Unit → IO String := runCharMvInt 2 2
def SympyMvInt.n2k2 : Unit → IO String := sympyMvInt 2 2
setup_fixed_benchmark MvInt.n2k2 where carrierConfig
setup_fixed_benchmark SympyMvInt.n2k2 where sympyConfig

def MvInt.n3k2 : Unit → IO String := runCharMvInt 3 2
def SympyMvInt.n3k2 : Unit → IO String := sympyMvInt 3 2
setup_fixed_benchmark MvInt.n3k2 where carrierConfig
setup_fixed_benchmark SympyMvInt.n3k2 where sympyConfig

def MvInt.n4k2 : Unit → IO String := runCharMvInt 4 2
def SympyMvInt.n4k2 : Unit → IO String := sympyMvInt 4 2
setup_fixed_benchmark MvInt.n4k2 where carrierConfig
setup_fixed_benchmark SympyMvInt.n4k2 where sympyConfig

def MvInt.n3k4 : Unit → IO String := runCharMvInt 3 4
def SympyMvInt.n3k4 : Unit → IO String := sympyMvInt 3 4
setup_fixed_benchmark MvInt.n3k4 where carrierConfig
setup_fixed_benchmark SympyMvInt.n3k4 where sympyConfig

def MvInt.n3k6 : Unit → IO String := runCharMvInt 3 6
def SympyMvInt.n3k6 : Unit → IO String := sympyMvInt 3 6
setup_fixed_benchmark MvInt.n3k6 where carrierConfig
setup_fixed_benchmark SympyMvInt.n3k6 where sympyConfig

def MvRat.n2k2 : Unit → IO String := runCharMvRat 2 2
def SympyMvRat.n2k2 : Unit → IO String := sympyMvRat 2 2
setup_fixed_benchmark MvRat.n2k2 where carrierConfig
setup_fixed_benchmark SympyMvRat.n2k2 where sympyConfig

def MvRat.n3k2 : Unit → IO String := runCharMvRat 3 2
def SympyMvRat.n3k2 : Unit → IO String := sympyMvRat 3 2
setup_fixed_benchmark MvRat.n3k2 where carrierConfig
setup_fixed_benchmark SympyMvRat.n3k2 where sympyConfig

def MvRat.n4k2 : Unit → IO String := runCharMvRat 4 2
def SympyMvRat.n4k2 : Unit → IO String := sympyMvRat 4 2
setup_fixed_benchmark MvRat.n4k2 where carrierConfig
setup_fixed_benchmark SympyMvRat.n4k2 where sympyConfig

def MvRat.n3k4 : Unit → IO String := runCharMvRat 3 4
def SympyMvRat.n3k4 : Unit → IO String := sympyMvRat 3 4
setup_fixed_benchmark MvRat.n3k4 where carrierConfig
setup_fixed_benchmark SympyMvRat.n3k4 where sympyConfig

def MvRat.n3k6 : Unit → IO String := runCharMvRat 3 6
def SympyMvRat.n3k6 : Unit → IO String := sympyMvRat 3 6
setup_fixed_benchmark MvRat.n3k6 where carrierConfig
setup_fixed_benchmark SympyMvRat.n3k6 where sympyConfig

def RatFn.n2k1 : Unit → IO String := runCharRatFn 2 1
def SympyRatFn.n2k1 : Unit → IO String := sympyRatFn 2 1
setup_fixed_benchmark RatFn.n2k1 where carrierConfig
setup_fixed_benchmark SympyRatFn.n2k1 where sympyConfig

def RatFn.n3k1 : Unit → IO String := runCharRatFn 3 1
def SympyRatFn.n3k1 : Unit → IO String := sympyRatFn 3 1
setup_fixed_benchmark RatFn.n3k1 where carrierConfig
setup_fixed_benchmark SympyRatFn.n3k1 where sympyConfig

def RatFn.n4k1 : Unit → IO String := runCharRatFn 4 1
def SympyRatFn.n4k1 : Unit → IO String := sympyRatFn 4 1
setup_fixed_benchmark RatFn.n4k1 where carrierConfig
setup_fixed_benchmark SympyRatFn.n4k1 where sympyConfig

def RatFn.n3k2 : Unit → IO String := runCharRatFn 3 2
def SympyRatFn.n3k2 : Unit → IO String := sympyRatFn 3 2
setup_fixed_benchmark RatFn.n3k2 where carrierConfig
setup_fixed_benchmark SympyRatFn.n3k2 where sympyConfig

def RatFn.n3k3 : Unit → IO String := runCharRatFn 3 3
def SympyRatFn.n3k3 : Unit → IO String := sympyRatFn 3 3
setup_fixed_benchmark RatFn.n3k3 where carrierConfig
setup_fixed_benchmark SympyRatFn.n3k3 where sympyConfig

private def emitPeak [Lean.Grind.CommRing R] [DecidableEq R]
    (encode : R → Json) (size : R → Nat) (family : String) (n k : Nat)
    (entry : Nat → Nat → R) : IO Unit := do
  let A := matrix entry "dense" n
  let (coeffs, maximum) := peak size A n (Nat.le_refl n)
  let actual := Json.arr (coeffs.reverse.toArray.map encode)
  if actual != Json.arr (A.charPoly.toArray.map encode) then
    throw (IO.userError "instrumented recurrence disagrees with charPoly")
  IO.println (Json.mkObj [("family", toJson family), ("n", toJson n),
    ("parameter", toJson k), ("peak", toJson maximum),
    ("checksum", toJson (hash actual.compress).toNat)]).compress

def carrierGrowth : IO UInt32 := do
  for (n, k) in [(2, 1), (3, 1), (4, 1), (3, 2), (3, 3)] do
    emitPeak (denseJson intJson) denseSize "DenseInt" n k (denseEntry id k)
    emitPeak (denseJson ratJson) denseSize "DenseRat" n k (denseEntry ratScalar k)
    emitPeak (denseJson modJson) denseSize "DenseMod" n k (denseEntry (fun z => (z : Mod)) k)
    emitPeak fractionJson fractionSize "RatFn" n k (ratFnEntry k)
  for (n, k) in [(2, 2), (3, 2), (4, 2), (3, 4), (3, 6)] do
    emitPeak (mvJson intJson) mvSize "MvInt" n k (mvEntry id 3 k)
    emitPeak (mvJson ratJson) mvSize "MvRat" n k (mvEntry ratScalar 3 k)
  return 0

/-- CI exercises Hex carrier registrations; external comparisons are explicit. -/
def verifyCI : IO UInt32 := do
  let parametric ← LeanBench.allRuntimeEntries
  let fixed ← LeanBench.allFixedRuntimeEntries
  let names := parametric.toList.map (fun e => e.spec.name.toString) ++
    (fixed.toList.filter (fun e => !e.spec.config.tags.contains "scheduled-only")).map
      (fun e => e.spec.name.toString)
  LeanBench.Cli.dispatch ("verify" :: names)

end Hex.CharPolyBench

def main (args : List String) : IO UInt32 :=
  match args with
  | ["carrier-growth"] => Hex.CharPolyBench.carrierGrowth
  | ["verify-ci"] => Hex.CharPolyBench.verifyCI
  | ["growth"] => Hex.CharPolyBench.growthReport
  | _ => LeanBench.Cli.dispatch args
