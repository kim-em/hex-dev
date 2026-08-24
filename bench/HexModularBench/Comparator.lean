/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexModular
import Hex.BenchOracle.Modular
import Lean.Data.Json
import LeanBench

/-!
# HexModular external-comparator registrations

The fixed pairs below cover every rung of the corresponding scientific
schedule. Input construction and request compression happen lazily during the
discarded first iteration, outside LeanBench's timed region. External calls
use the persistent service in `scripts/oracle/modular_bench_driver.py`; that
discarded iteration also starts Python and imports `gmpy2` and python-flint
before timing.

* `gmpy2.gcdext` is paired with a complete Fibonacci-shaped
  `euclidUntil` run.
* python-flint `fmpz_mod_ctx` Garner steps are paired with scalar CRT depth
  and fixed-depth vector CRT width ladders.

The driver returns exact results to Lean. Every pair therefore has the same
observed hash, making `bench compare` a differential check as well as a timing
comparison.
-/

namespace Hex.ModularBench.Comparator

open Hex
open Hex.Modular
open Lean (Json JsonNumber)

def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

def hashRow (r t : Int) : UInt64 := mixWord (hash r) (hash t)

def hashCrt (modulus : Nat) (value : Int) : UInt64 :=
  mixWord 1 (mixWord (hash modulus) (hash value))

def hashCrtVec (modulus : Nat) (values : Array Int) : UInt64 :=
  mixWord 1 <| values.foldl (fun acc value => mixWord acc (hash value))
    (hash modulus)

def intJson (value : Int) : Json := Json.num (JsonNumber.fromInt value)

def natJson (value : Nat) : Json := intJson (Int.ofNat value)

def request (op : String) (fields : List (String × Json)) : String :=
  Json.mkObj (("op", Json.str op) :: fields) |>.compress

def parseIntPair (result : Json) : IO (Int × Int) := do
  let values ← match result.getArr? with
    | .ok values => pure values
    | .error error => throw <| IO.userError s!"comparator expected pair: {error}"
  let some left := values[0]?
    | throw <| IO.userError "comparator pair omitted its first element"
  let some right := values[1]?
    | throw <| IO.userError "comparator pair omitted its second element"
  let left ← match left.getInt? with
    | .ok value => pure value
    | .error error => throw <| IO.userError s!"comparator pair: {error}"
  let right ← match right.getInt? with
    | .ok value => pure value
    | .error error => throw <| IO.userError s!"comparator pair: {error}"
  return (left, right)

def fibonacciPair (steps : Nat) : Nat × Nat :=
  (List.range steps).foldl (fun pair _ => (pair.2, pair.1 + pair.2)) (1, 1)

structure GcdCase where
  modulus : Nat
  residue : Int
  line : String
  deriving Inhabited

def makeGcdCase (bits : Nat) : GcdCase :=
  let pair := fibonacciPair (3 * bits / 2 + 3)
  { modulus := pair.2
    residue := Int.ofNat pair.1
    line := request "gmpy2_gcdext"
      [("m", natJson pair.2), ("a", natJson pair.1)] }

def runLeanGcd (input : GcdCase) : UInt64 :=
  let row := euclidUntil (Int.ofNat input.modulus) input.residue 1
  hashRow row.r row.t

def runGmpy2Gcd (input : GcdCase) : IO UInt64 := do
  let (gcd, coefficient) ←
    parseIntPair (← Hex.BenchOracle.Modular.runLine input.line)
  return hashRow gcd coefficient

def smallPrimes (count : Nat) : Array Nat :=
  ((List.range (32 * count + 100)).drop 2).filter Hex.Nat.isPrimeTrial
    |>.take count |>.toArray

def wordPrimePower (prime : Nat) : Nat :=
  prime ^ (30 / max 1 prime.log2)

def moduli (count : Nat) : Array Nat :=
  (smallPrimes count).map wordPrimePower

def residue (index modulus salt : Nat) : Int :=
  Int.ofNat ((index * 1_103_515_245 + salt * 12_345 + 97) % modulus)

structure ScalarCase where
  entries : Array (Int × Nat)
  line : String
  deriving Inhabited

def scalarEntriesJson (entries : Array (Int × Nat)) : Json :=
  Json.arr <| entries.map fun entry => Json.arr #[intJson entry.1, natJson entry.2]

def makeScalarCase (depth : Nat) : ScalarCase :=
  let entries := (moduli depth).mapIdx fun index modulus =>
    (residue index modulus 11, modulus)
  { entries
    line := request "flint_crt" [("entries", scalarEntriesJson entries)] }

def runLeanScalar (input : ScalarCase) : UInt64 :=
  let answer := input.entries.foldl
    (fun state entry => state.bind fun current => current.push entry.1 entry.2)
    (some Crt.init)
  match answer with
  | none => 0
  | some state => hashCrt state.modulus state.value

def runFlintScalar (input : ScalarCase) : IO UInt64 := do
  let (modulus, value) ←
    parseIntPair (← Hex.BenchOracle.Modular.runLine input.line)
  if modulus < 0 then
    throw <| IO.userError "FLINT CRT returned a negative modulus"
  return hashCrt modulus.toNat value

structure VectorCase where
  width : Nat
  entries : Array (Vector Int width × Nat)
  line : String
  deriving Inhabited

def vectorEntriesJson {width : Nat}
    (entries : Array (Vector Int width × Nat)) : Json :=
  Json.arr <| entries.map fun entry =>
    Json.arr #[Json.arr (entry.1.toArray.map intJson), natJson entry.2]

def makeVectorCase (width : Nat) : VectorCase :=
  let entries := (moduli 16).mapIdx fun index modulus =>
    (Vector.ofFn fun coordinate =>
      residue (index + coordinate.val) modulus 23, modulus)
  { width, entries
    line := request "flint_crt_vec" [("entries", vectorEntriesJson entries)] }

def runLeanVector (input : VectorCase) : UInt64 :=
  let answer := input.entries.foldl
    (fun state entry => state.bind fun current => current.push entry.1 entry.2)
    (some (CrtVec.init input.width))
  match answer with
  | none => 0
  | some state => hashCrtVec state.modulus state.value.toArray

def parseVectorResult (result : Json) : IO (Nat × Array Int) := do
  let values ← match result.getArr? with
    | .ok values => pure values
    | .error error => throw <| IO.userError s!"FLINT vector CRT: {error}"
  let some modulusJson := values[0]?
    | throw <| IO.userError "FLINT vector CRT omitted its modulus"
  let some entriesJson := values[1]?
    | throw <| IO.userError "FLINT vector CRT omitted its values"
  let modulus ← match modulusJson.getNat? with
    | .ok value => pure value
    | .error error => throw <| IO.userError s!"FLINT vector CRT: {error}"
  let entries ← Hex.BenchOracle.Flint.jsonToInts entriesJson
  return (modulus, entries.toArray)

def runFlintVector (input : VectorCase) : IO UInt64 := do
  let (modulus, values) ←
    parseVectorResult (← Hex.BenchOracle.Modular.runLine input.line)
  return hashCrtVec modulus values

def leanConfig : LeanBench.FixedBenchmarkConfig :=
  -- The parent watchdog covers the discarded lazy-fixture warmup as well as
  -- the measured call. The report's 10-second eligibility ceiling is applied
  -- to the exported per-call medians, not to this process-lifetime guard.
  { repeats := 5, minTotalSeconds := 0.2, maxSecondsPerCall := 60.0,
    warmupFirstIter := true }

def externalConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, minTotalSeconds := 0.2, maxSecondsPerCall := 6.0,
    warmupFirstIter := true }

def runComparatorOverhead (_ : Unit) : IO Int := do
  let result ← Hex.BenchOracle.Modular.runLine (request "overhead" [])
  match result.getInt? with
  | .ok value => return value
  | .error error => throw <| IO.userError s!"comparator overhead: {error}"

/-! Prepared cases and fixed wrappers. -/

def cached (ref : IO.Ref (Option α)) (make : Unit → α) : IO α := do
  if let some value ← ref.get then
    return value
  let value := make ()
  ref.set (some value)
  return value

initialize gcd64 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd128 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd256 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd512 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd1024 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd2048 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd4096 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd8192 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd16384 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd32768 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd65536 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd100000 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd131072 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd196608 : IO.Ref (Option GcdCase) ← IO.mkRef none
initialize gcd262144 : IO.Ref (Option GcdCase) ← IO.mkRef none

def leanGcd (input : IO.Ref (Option GcdCase)) (bits : Nat) : Unit → IO UInt64 := fun _ =>
  return runLeanGcd (← cached input fun _ => makeGcdCase bits)
def externalGcd (input : IO.Ref (Option GcdCase)) (bits : Nat) : Unit → IO UInt64 := fun _ => do
  runGmpy2Gcd (← cached input fun _ => makeGcdCase bits)

def runLeanGcd64 := leanGcd gcd64 64
def runGmpy2Gcd64 := externalGcd gcd64 64
def runLeanGcd128 := leanGcd gcd128 128
def runGmpy2Gcd128 := externalGcd gcd128 128
def runLeanGcd256 := leanGcd gcd256 256
def runGmpy2Gcd256 := externalGcd gcd256 256
def runLeanGcd512 := leanGcd gcd512 512
def runGmpy2Gcd512 := externalGcd gcd512 512
def runLeanGcd1024 := leanGcd gcd1024 1024
def runGmpy2Gcd1024 := externalGcd gcd1024 1024
def runLeanGcd2048 := leanGcd gcd2048 2048
def runGmpy2Gcd2048 := externalGcd gcd2048 2048
def runLeanGcd4096 := leanGcd gcd4096 4096
def runGmpy2Gcd4096 := externalGcd gcd4096 4096
def runLeanGcd8192 := leanGcd gcd8192 8192
def runGmpy2Gcd8192 := externalGcd gcd8192 8192
def runLeanGcd16384 := leanGcd gcd16384 16384
def runGmpy2Gcd16384 := externalGcd gcd16384 16384
def runLeanGcd32768 := leanGcd gcd32768 32768
def runGmpy2Gcd32768 := externalGcd gcd32768 32768
def runLeanGcd65536 := leanGcd gcd65536 65536
def runGmpy2Gcd65536 := externalGcd gcd65536 65536
def runLeanGcd100000 := leanGcd gcd100000 100000
def runGmpy2Gcd100000 := externalGcd gcd100000 100000
def runLeanGcd131072 := leanGcd gcd131072 131072
def runGmpy2Gcd131072 := externalGcd gcd131072 131072
def runLeanGcd196608 := leanGcd gcd196608 196608
def runGmpy2Gcd196608 := externalGcd gcd196608 196608
def runLeanGcd262144 := leanGcd gcd262144 262144
def runGmpy2Gcd262144 := externalGcd gcd262144 262144

initialize scalar4 : IO.Ref (Option ScalarCase) ← IO.mkRef none
initialize scalar8 : IO.Ref (Option ScalarCase) ← IO.mkRef none
initialize scalar16 : IO.Ref (Option ScalarCase) ← IO.mkRef none
initialize scalar32 : IO.Ref (Option ScalarCase) ← IO.mkRef none
initialize scalar64 : IO.Ref (Option ScalarCase) ← IO.mkRef none
initialize scalar128 : IO.Ref (Option ScalarCase) ← IO.mkRef none
initialize scalar256 : IO.Ref (Option ScalarCase) ← IO.mkRef none
initialize scalar512 : IO.Ref (Option ScalarCase) ← IO.mkRef none
initialize scalar1024 : IO.Ref (Option ScalarCase) ← IO.mkRef none
initialize scalar2048 : IO.Ref (Option ScalarCase) ← IO.mkRef none
initialize scalar4096 : IO.Ref (Option ScalarCase) ← IO.mkRef none
initialize scalar8192 : IO.Ref (Option ScalarCase) ← IO.mkRef none

def leanScalar (input : IO.Ref (Option ScalarCase)) (depth : Nat) : Unit → IO UInt64 := fun _ =>
  return runLeanScalar (← cached input fun _ => makeScalarCase depth)
def externalScalar (input : IO.Ref (Option ScalarCase)) (depth : Nat) : Unit → IO UInt64 := fun _ => do
  runFlintScalar (← cached input fun _ => makeScalarCase depth)

def runLeanScalar4 := leanScalar scalar4 4
def runFlintScalar4 := externalScalar scalar4 4
def runLeanScalar8 := leanScalar scalar8 8
def runFlintScalar8 := externalScalar scalar8 8
def runLeanScalar16 := leanScalar scalar16 16
def runFlintScalar16 := externalScalar scalar16 16
def runLeanScalar32 := leanScalar scalar32 32
def runFlintScalar32 := externalScalar scalar32 32
def runLeanScalar64 := leanScalar scalar64 64
def runFlintScalar64 := externalScalar scalar64 64
def runLeanScalar128 := leanScalar scalar128 128
def runFlintScalar128 := externalScalar scalar128 128
def runLeanScalar256 := leanScalar scalar256 256
def runFlintScalar256 := externalScalar scalar256 256
def runLeanScalar512 := leanScalar scalar512 512
def runFlintScalar512 := externalScalar scalar512 512
def runLeanScalar1024 := leanScalar scalar1024 1024
def runFlintScalar1024 := externalScalar scalar1024 1024
def runLeanScalar2048 := leanScalar scalar2048 2048
def runFlintScalar2048 := externalScalar scalar2048 2048
def runLeanScalar4096 := leanScalar scalar4096 4096
def runFlintScalar4096 := externalScalar scalar4096 4096
def runLeanScalar8192 := leanScalar scalar8192 8192
def runFlintScalar8192 := externalScalar scalar8192 8192

initialize vector1 : IO.Ref (Option VectorCase) ← IO.mkRef none
initialize vector4 : IO.Ref (Option VectorCase) ← IO.mkRef none
initialize vector16 : IO.Ref (Option VectorCase) ← IO.mkRef none
initialize vector64 : IO.Ref (Option VectorCase) ← IO.mkRef none
initialize vector256 : IO.Ref (Option VectorCase) ← IO.mkRef none
initialize vector1024 : IO.Ref (Option VectorCase) ← IO.mkRef none
initialize vector2048 : IO.Ref (Option VectorCase) ← IO.mkRef none
initialize vector4096 : IO.Ref (Option VectorCase) ← IO.mkRef none

def leanVector (input : IO.Ref (Option VectorCase)) (width : Nat) : Unit → IO UInt64 := fun _ =>
  return runLeanVector (← cached input fun _ => makeVectorCase width)
def externalVector (input : IO.Ref (Option VectorCase)) (width : Nat) : Unit → IO UInt64 := fun _ => do
  runFlintVector (← cached input fun _ => makeVectorCase width)

def runLeanVector1 := leanVector vector1 1
def runFlintVector1 := externalVector vector1 1
def runLeanVector4 := leanVector vector4 4
def runFlintVector4 := externalVector vector4 4
def runLeanVector16 := leanVector vector16 16
def runFlintVector16 := externalVector vector16 16
def runLeanVector64 := leanVector vector64 64
def runFlintVector64 := externalVector vector64 64
def runLeanVector256 := leanVector vector256 256
def runFlintVector256 := externalVector vector256 256
def runLeanVector1024 := leanVector vector1024 1024
def runFlintVector1024 := externalVector vector1024 1024
def runLeanVector2048 := leanVector vector2048 2048
def runFlintVector2048 := externalVector vector2048 2048
def runLeanVector4096 := leanVector vector4096 4096
def runFlintVector4096 := externalVector vector4096 4096

/-! Full-ladder fixed registrations. -/

setup_fixed_benchmark runComparatorOverhead where externalConfig

setup_fixed_benchmark runLeanGcd64 where leanConfig
setup_fixed_benchmark runGmpy2Gcd64 where externalConfig
setup_fixed_benchmark runLeanGcd128 where leanConfig
setup_fixed_benchmark runGmpy2Gcd128 where externalConfig
setup_fixed_benchmark runLeanGcd256 where leanConfig
setup_fixed_benchmark runGmpy2Gcd256 where externalConfig
setup_fixed_benchmark runLeanGcd512 where leanConfig
setup_fixed_benchmark runGmpy2Gcd512 where externalConfig
setup_fixed_benchmark runLeanGcd1024 where leanConfig
setup_fixed_benchmark runGmpy2Gcd1024 where externalConfig
setup_fixed_benchmark runLeanGcd2048 where leanConfig
setup_fixed_benchmark runGmpy2Gcd2048 where externalConfig
setup_fixed_benchmark runLeanGcd4096 where leanConfig
setup_fixed_benchmark runGmpy2Gcd4096 where externalConfig
setup_fixed_benchmark runLeanGcd8192 where leanConfig
setup_fixed_benchmark runGmpy2Gcd8192 where externalConfig
setup_fixed_benchmark runLeanGcd16384 where leanConfig
setup_fixed_benchmark runGmpy2Gcd16384 where externalConfig
setup_fixed_benchmark runLeanGcd32768 where leanConfig
setup_fixed_benchmark runGmpy2Gcd32768 where externalConfig
setup_fixed_benchmark runLeanGcd65536 where leanConfig
setup_fixed_benchmark runGmpy2Gcd65536 where externalConfig
setup_fixed_benchmark runLeanGcd100000 where leanConfig
setup_fixed_benchmark runGmpy2Gcd100000 where externalConfig
setup_fixed_benchmark runLeanGcd131072 where leanConfig
setup_fixed_benchmark runGmpy2Gcd131072 where externalConfig
setup_fixed_benchmark runLeanGcd196608 where leanConfig
setup_fixed_benchmark runGmpy2Gcd196608 where externalConfig
setup_fixed_benchmark runLeanGcd262144 where leanConfig
setup_fixed_benchmark runGmpy2Gcd262144 where externalConfig

setup_fixed_benchmark runLeanScalar4 where leanConfig
setup_fixed_benchmark runFlintScalar4 where externalConfig
setup_fixed_benchmark runLeanScalar8 where leanConfig
setup_fixed_benchmark runFlintScalar8 where externalConfig
setup_fixed_benchmark runLeanScalar16 where leanConfig
setup_fixed_benchmark runFlintScalar16 where externalConfig
setup_fixed_benchmark runLeanScalar32 where leanConfig
setup_fixed_benchmark runFlintScalar32 where externalConfig
setup_fixed_benchmark runLeanScalar64 where leanConfig
setup_fixed_benchmark runFlintScalar64 where externalConfig
setup_fixed_benchmark runLeanScalar128 where leanConfig
setup_fixed_benchmark runFlintScalar128 where externalConfig
setup_fixed_benchmark runLeanScalar256 where leanConfig
setup_fixed_benchmark runFlintScalar256 where externalConfig
setup_fixed_benchmark runLeanScalar512 where leanConfig
setup_fixed_benchmark runFlintScalar512 where externalConfig
setup_fixed_benchmark runLeanScalar1024 where leanConfig
setup_fixed_benchmark runFlintScalar1024 where externalConfig
setup_fixed_benchmark runLeanScalar2048 where leanConfig
setup_fixed_benchmark runFlintScalar2048 where externalConfig
setup_fixed_benchmark runLeanScalar4096 where leanConfig
setup_fixed_benchmark runFlintScalar4096 where externalConfig
setup_fixed_benchmark runLeanScalar8192 where leanConfig
setup_fixed_benchmark runFlintScalar8192 where externalConfig

setup_fixed_benchmark runLeanVector1 where leanConfig
setup_fixed_benchmark runFlintVector1 where externalConfig
setup_fixed_benchmark runLeanVector4 where leanConfig
setup_fixed_benchmark runFlintVector4 where externalConfig
setup_fixed_benchmark runLeanVector16 where leanConfig
setup_fixed_benchmark runFlintVector16 where externalConfig
setup_fixed_benchmark runLeanVector64 where leanConfig
setup_fixed_benchmark runFlintVector64 where externalConfig
setup_fixed_benchmark runLeanVector256 where leanConfig
setup_fixed_benchmark runFlintVector256 where externalConfig
setup_fixed_benchmark runLeanVector1024 where leanConfig
setup_fixed_benchmark runFlintVector1024 where externalConfig
setup_fixed_benchmark runLeanVector2048 where leanConfig
setup_fixed_benchmark runFlintVector2048 where externalConfig
setup_fixed_benchmark runLeanVector4096 where leanConfig
setup_fixed_benchmark runFlintVector4096 where externalConfig

end Hex.ModularBench.Comparator
