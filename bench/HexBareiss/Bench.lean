/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBareiss
import HexPolyFp.PrimeField
import HexResultant.ExactDiv
import HexMvGcd.Divide
import HexMvGcd.Instances
import Hex.BenchOracle.Carriers
import Hex.BenchOracle.Flint
import Lean.Data.Json
import LeanBench

/-!
Benchmark registrations for `hex-bareiss`.

This Phase 4 slice measures the executable row-pivoted Bareiss determinant over
`Int` on deterministically generated integer inputs. Matrix construction is
hoisted into `prep` so the declared model tracks the timed elimination loop
rather than fixture construction.

Scientific registration:

* `runBareissDet`: row-pivoted Bareiss determinant over `Int`, `O(n^3)`.

Informational external comparator (FLINT `fmpz_mat_det` via the shared
persistent-subprocess python-flint driver, per
`SPEC/Libraries/hex-bareiss.md §"External comparators"` and
`SPEC/benchmarking.md §"External comparators" §"Process call"`):

* `runFlintBareissDet*` ↔ `runBareissDet*` (`fmpz_mat.det`).

FLINT's determinant uses multimodular reduction + CRT, structurally different
from Hex's fraction-free Bareiss elimination; the ratio is recorded for
orientation but does not block Phase 4.
-/

namespace Hex.BareissBench

/-- Flattened benchmark input for one square integer matrix. -/
structure DetInput where
  n : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

/-- Deterministic tridiagonal entries for determinant benchmarks. The shape
keeps Bareiss intermediates small so the registration tests elimination-loop
scaling rather than arbitrary-precision integer growth in random minors. -/
def smallEntryValue (_n row col salt : Nat) : Int :=
  if row = col then
    2 + (salt % 2)
  else if row + 1 = col then
    -1
  else if col + 1 = row then
    1
  else
    0

/-- Deterministic small-entry row-major matrix fixture of shape `n × n`. -/
def flatSmallMatrix (n salt : Nat) : Array Int :=
  if n = 0 then
    #[]
  else
    (Array.range (n * n)).map fun idx =>
      let row := idx / n
      let col := idx % n
      smallEntryValue n row col salt

/-- Per-parameter determinant fixture: one deterministic square matrix. -/
def prepDetInput (n : Nat) : DetInput :=
  { n := n
    entries := flatSmallMatrix n 71 }

/-- Reconstruct a typed dense square matrix from a row-major array. -/
def matrixOfFlat (n : Nat) (entries : Array Int) : Hex.Matrix Int n n :=
  Hex.Matrix.ofFn fun i j => entries.getD (i.val * n + j.val) 0

/-- Benchmark target: compute the determinant using row-pivoted Bareiss
elimination. Fixture construction is supplied by `prepDetInput`. -/
def runBareissDet (input : DetInput) : Int :=
  let M : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.entries
  Hex.Matrix.bareiss M

/-- Internal quotient-path comparison: run the same generic Bareiss algorithm
through the guarded, `Div`-derived exact quotient. This is not an external
comparator and does not replace the `Int` benchmark above. -/
def runBareissGenericDet (input : DetInput) : Int :=
  let M : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.entries
  Hex.Matrix.bareissWith Hex.exactDiv M

/-- Encode a row-major `n × n` integer matrix fixture as the JSON 2D
array shape FLINT's `fmpz_mat` family accepts (`rows: [[…], …]`). -/
def flatToFlintRows (n : Nat) (entries : Array Int) : Lean.Json :=
  let rows : Array Lean.Json := (Array.range n).map fun i =>
    let row := (Array.range n).map fun j => entries.getD (i * n + j) 0
    Hex.BenchOracle.Flint.intsToJson row.toList
  Lean.Json.arr rows

/-- FLINT comparator: `fmpz_mat.det`. Returns the determinant directly
(matches `runBareissDet` on the same prepared input, modulo Bareiss's
single sign convention from row pivoting versus FLINT's multimodular
result). -/
def runFlintBareissDet (input : DetInput) : IO Int := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mat" "det"
    #[("rows", flatToFlintRows input.n input.entries)]
  match result.getInt? with
  | Except.ok n => return n
  | Except.error msg =>
      throw <| IO.userError s!"FLINT fmpz_mat.det result not integer: {msg}"

/-- Persistent FLINT framing and dispatch calibration without matrix work. -/
def runFlintOverhead (_ : Unit) : IO Int := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mat" "overhead" #[]
  match result.getInt? with
  | .ok 0 => return 0
  | .ok value =>
      throw <| IO.userError s!"FLINT overhead result was {value}, expected zero"
  | .error message =>
      throw <| IO.userError s!"FLINT overhead result not integer: {message}"

/-! Per-rung wrappers for paired fixed-benchmark registrations. Each wrapper
captures `prepDetInput n` outside its returned timed closure, so the Hex target
and FLINT comparator operate on the same prepared input without charging
fixture construction to either arm. -/

def runBareissDetAt (n : Nat) : Unit → IO Int :=
  let input := prepDetInput n
  fun _ => return runBareissDet input
def runBareissGenericDetAt (n : Nat) : Unit → IO Int :=
  let input := prepDetInput n
  fun _ => return runBareissGenericDet input
def runFlintBareissDetAt (n : Nat) : Unit → IO Int :=
  let input := prepDetInput n
  fun _ => runFlintBareissDet input

/-! Per-rung concrete bindings used by `setup_fixed_benchmark`. The
rung ladder densifies the parametric `[8, 12, 16]` schedule outward
toward sizes where FLINT's per-call wall time clears the persistent-
subprocess startup floor, while staying inside the 10 s hard / 1 s
soft per-call ceiling (per `SPEC/benchmarking.md §"Headline reports"
§"Comparator ratios"`). The tridiagonal `flatSmallMatrix` fixture
keeps Bareiss intermediates bounded so the cubic in `n` scales the
elimination loop, not bigint operand growth. -/

def runBareissDet16 : Unit → IO Int := runBareissDetAt 16
def runFlintBareissDet16 : Unit → IO Int := runFlintBareissDetAt 16
def runBareissDet24 : Unit → IO Int := runBareissDetAt 24
def runFlintBareissDet24 : Unit → IO Int := runFlintBareissDetAt 24
def runBareissDet32 : Unit → IO Int := runBareissDetAt 32
def runFlintBareissDet32 : Unit → IO Int := runFlintBareissDetAt 32
def runBareissDet48 : Unit → IO Int := runBareissDetAt 48
def runFlintBareissDet48 : Unit → IO Int := runFlintBareissDetAt 48
def runBareissDet64 : Unit → IO Int := runBareissDetAt 64
def runFlintBareissDet64 : Unit → IO Int := runFlintBareissDetAt 64
def runBareissDet96 : Unit → IO Int := runBareissDetAt 96
def runFlintBareissDet96 : Unit → IO Int := runFlintBareissDetAt 96
def runBareissDet128 : Unit → IO Int := runBareissDetAt 128
def runFlintBareissDet128 : Unit → IO Int := runFlintBareissDetAt 128
def runBareissDet192 : Unit → IO Int := runBareissDetAt 192
def runFlintBareissDet192 : Unit → IO Int := runFlintBareissDetAt 192
def runBareissDet256 : Unit → IO Int := runBareissDetAt 256
def runBareissGenericDet256 : Unit → IO Int := runBareissGenericDetAt 256
def runFlintBareissDet256 : Unit → IO Int := runFlintBareissDetAt 256
def runBareissDet320 : Unit → IO Int := runBareissDetAt 320
def runFlintBareissDet320 : Unit → IO Int := runFlintBareissDetAt 320
def runBareissDet384 : Unit → IO Int := runBareissDetAt 384
def runBareissGenericDet384 : Unit → IO Int := runBareissGenericDetAt 384
def runFlintBareissDet384 : Unit → IO Int := runFlintBareissDetAt 384
def runBareissDet512 : Unit → IO Int := runBareissDetAt 512
def runFlintBareissDet512 : Unit → IO Int := runFlintBareissDetAt 512

/-! `runBareissDet` cost model: row-pivoted Bareiss fraction-free elimination
performs `O(n^3)` field-style operations across the `n` elimination stages, so
the declared model is `n * n * n`. -/
setup_benchmark runBareissDet n => n * n * n
  with prep := prepDetInput
  where {
    paramFloor := 8
    paramCeiling := 16
    paramSchedule := .custom #[8, 12, 16]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 2000000000
  }

/-! # FLINT `fmpz_mat_det` informational comparator fixed registrations

`runBareissDet` is paired with the FLINT `fmpz_mat.det` op via the
shared persistent-subprocess driver. The pairs are registered as
`setup_fixed_benchmark` rungs across a densified ladder so the
headline report records raw and overhead-adjusted ratios at each rung
and a trend across the ladder. The comparator is `informational` per
`HexBareiss/SPEC/hex-bareiss.md §"External comparators"`: no
gating-goal verdict is required; the ratios are recorded for
orientation. Both arms discard one call and use the same 200 ms inner-batch
floor, so driver startup and first-use effects are outside timing. -/

def leanCompareConfig (maxSeconds : Float) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := maxSeconds, minTotalSeconds := 0.2,
    warmupFirstIter := true }

def flintCompareConfig (maxSeconds : Float) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := maxSeconds, minTotalSeconds := 0.2,
    warmupFirstIter := true }

setup_fixed_benchmark runFlintOverhead where flintCompareConfig 6.0

setup_fixed_benchmark runBareissDet16 where leanCompareConfig 6.0
setup_fixed_benchmark runFlintBareissDet16 where flintCompareConfig 6.0
setup_fixed_benchmark runBareissDet24 where leanCompareConfig 6.0
setup_fixed_benchmark runFlintBareissDet24 where flintCompareConfig 6.0
setup_fixed_benchmark runBareissDet32 where leanCompareConfig 6.0
setup_fixed_benchmark runFlintBareissDet32 where flintCompareConfig 6.0
setup_fixed_benchmark runBareissDet48 where leanCompareConfig 6.0
setup_fixed_benchmark runFlintBareissDet48 where flintCompareConfig 6.0
setup_fixed_benchmark runBareissDet64 where leanCompareConfig 6.0
setup_fixed_benchmark runFlintBareissDet64 where flintCompareConfig 6.0
setup_fixed_benchmark runBareissDet96 where leanCompareConfig 6.0
setup_fixed_benchmark runFlintBareissDet96 where flintCompareConfig 6.0
setup_fixed_benchmark runBareissDet128 where leanCompareConfig 6.0
setup_fixed_benchmark runFlintBareissDet128 where flintCompareConfig 6.0
setup_fixed_benchmark runBareissDet192 where leanCompareConfig 6.0
setup_fixed_benchmark runFlintBareissDet192 where flintCompareConfig 6.0
setup_fixed_benchmark runBareissDet256 where leanCompareConfig 6.0
setup_fixed_benchmark runBareissGenericDet256 where leanCompareConfig 6.0
setup_fixed_benchmark runFlintBareissDet256 where flintCompareConfig 6.0
setup_fixed_benchmark runBareissDet320 where leanCompareConfig 8.0
setup_fixed_benchmark runFlintBareissDet320 where flintCompareConfig 8.0
setup_fixed_benchmark runBareissDet384 where leanCompareConfig 12.0
setup_fixed_benchmark runBareissGenericDet384 where leanCompareConfig 12.0
setup_fixed_benchmark runFlintBareissDet384 where flintCompareConfig 12.0
setup_fixed_benchmark runBareissDet512 where leanCompareConfig 25.0
setup_fixed_benchmark runFlintBareissDet512 where flintCompareConfig 25.0


/-! Carrier sweeps. Dense inputs have two nonzero coefficients while degree
varies. Sparse inputs have arity three and total degree two while support varies.
The tridiagonal leading minors force polynomial exact division from step one;
the final determinant is not obtained by multiplying triangular entries.
These fixed points record timings without asserting a bit-complexity model.
Input construction and request encoding are outside the timed closures.
-/

instance : ZMod64.Bounds 101 := ⟨by decide, by decide⟩
instance : ZMod64.PrimeModulus 101 := ZMod64.primeModulusOfPrime (by decide)
abbrev Mod := ZMod64 101
abbrev Mv (R : Type) [Zero R] := MvPoly 3 R Mono.grevlex

private def ratJson (q : Rat) : Lean.Json := Lean.toJson #[Lean.toJson q.num, Lean.toJson q.den]
private def modJson (q : Mod) : Lean.Json := Lean.toJson q.toNat
private def denseJson {R : Type} [Zero R] [DecidableEq R]
    (encode : R → Lean.Json) (f : DensePoly R) : Lean.Json :=
  Lean.toJson (f.toArray.map encode)
private def mvJson {R : Type} [Zero R] (encode : R → Lean.Json) (f : Mv R) : Lean.Json :=
  Lean.toJson (f.termsList.map fun (m, c) => Lean.toJson #[Lean.toJson m.toList, encode c])

private def carrierMatrix {R : Type} [Zero R] [One R] [Add R] [Neg R]
    (n : Nat) (x : R) : Matrix R n n :=
  Matrix.ofFn fun i j =>
    if i.val = j.val then x + 1
    else if i.val + 1 = j.val then 1
    else if j.val + 1 = i.val then -1 else 0

private def denseEntry {R : Type} [Lean.Grind.CommRing R] [DecidableEq R]
    (degree : Nat) (a : R) : DensePoly R :=
  DensePoly.ofCoeffs ((Array.range (degree + 1)).map fun i =>
    if i = 0 then 1 else if i = degree then a else 0)

private def mvEntry {R : Type} [Lean.Grind.CommRing R] [DecidableEq R]
    [BEq R] [LawfulBEq R] (terms : Nat) (a : R) : Mv R :=
  let x : Mv R := MvPoly.X 0
  let y : Mv R := MvPoly.X 1
  let z : Mv R := MvPoly.X 2
  (#[MvPoly.C a * (x * y), y * z, x * z, x * x]).toList.take terms |>.foldl (· + ·) 0

private def hexCarrier {R : Type} [Zero R] [One R] [Add R] [Neg R] [Sub R] [Mul R]
    [DecidableEq R] [Div R]
    (n : Nat) (x : R) (encode : R → Lean.Json) : Unit → IO String :=
  let matrix := carrierMatrix n x
  fun _ => return (encode (Matrix.bareissWith Hex.exactDiv matrix)).compress

private def oracleCarrier {R : Type} [Zero R] [One R] [Add R] [Neg R]
    (carrier : String) (arity n : Nat) (x : R) (encode : R → Lean.Json) : Unit → IO String :=
  let matrix := carrierMatrix n x
  let line := (Lean.Json.mkObj [
    ("kind", Lean.toJson "bareiss_carrier"), ("carrier", Lean.toJson carrier),
    ("n", Lean.toJson n), ("arity", Lean.toJson arity), ("p", Lean.toJson (101 : Nat)),
    ("rows", Lean.toJson (matrix.rows.toArray.map fun row => Lean.toJson (row.toArray.map encode)))]).compress
  fun _ => Hex.BenchOracle.Carriers.runLine line

private def carrierConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 10, minTotalSeconds := 0.2, warmupFirstIter := true }
private def scheduledTag := "scheduled-hardware"

private def oracleConfig : LeanBench.FixedBenchmarkConfig :=
  { carrierConfig with tags := #[scheduledTag] }

def runCarrierOverhead (_ : Unit) : IO String :=
  Hex.BenchOracle.Carriers.runLine "{\"kind\":\"overhead\"}"
setup_fixed_benchmark runCarrierOverhead where oracleConfig

def runBareissRat (n : Nat) : Unit → IO String :=
  hexCarrier n (3 / 2 : Rat) ratJson
def runOracleRat (n : Nat) : Unit → IO String :=
  oracleCarrier "rat" 0 n (3 / 2 : Rat) ratJson

def runBareissRatN4 := runBareissRat 4
def runOracleRatN4 := runOracleRat 4
setup_fixed_benchmark runBareissRatN4 where { carrierConfig with expectedHash := some 0xe4e39b79a543e513 }
setup_fixed_benchmark runOracleRatN4 where oracleConfig
def runBareissRatN8 := runBareissRat 8
def runOracleRatN8 := runOracleRat 8
setup_fixed_benchmark runBareissRatN8 where { carrierConfig with expectedHash := some 0xca1569d8226f229d }
setup_fixed_benchmark runOracleRatN8 where oracleConfig
def runBareissRatN16 := runBareissRat 16
def runOracleRatN16 := runOracleRat 16
setup_fixed_benchmark runBareissRatN16 where { carrierConfig with expectedHash := some 0xd5e3127ec7e5d3fe }
setup_fixed_benchmark runOracleRatN16 where oracleConfig

def runBareissMod (n : Nat) : Unit → IO String :=
  hexCarrier n (3 / 2 : Mod) modJson
def runOracleMod (n : Nat) : Unit → IO String :=
  oracleCarrier "mod" 0 n (3 / 2 : Mod) modJson

def runBareissModN4 := runBareissMod 4
def runOracleModN4 := runOracleMod 4
setup_fixed_benchmark runBareissModN4 where { carrierConfig with expectedHash := some 0x470384a52bef7e9e }
setup_fixed_benchmark runOracleModN4 where oracleConfig
def runBareissModN8 := runBareissMod 8
def runOracleModN8 := runOracleMod 8
setup_fixed_benchmark runBareissModN8 where { carrierConfig with expectedHash := some 0xc8c7afc9611ffff0 }
setup_fixed_benchmark runOracleModN8 where oracleConfig
def runBareissModN16 := runBareissMod 16
def runOracleModN16 := runOracleMod 16
setup_fixed_benchmark runBareissModN16 where { carrierConfig with expectedHash := some 0xa00b9350ae2c0b96 }
setup_fixed_benchmark runOracleModN16 where oracleConfig

def runBareissDenseRat (n degree : Nat) : Unit → IO String :=
  hexCarrier n (denseEntry degree (2 / 3 : Rat)) (denseJson ratJson)
def runOracleDenseRat (n degree : Nat) : Unit → IO String :=
  oracleCarrier "dense_rat" 1 n (denseEntry degree (2 / 3 : Rat)) (denseJson ratJson)

def runBareissDenseRatN3D1 := runBareissDenseRat 3 1
def runOracleDenseRatN3D1 := runOracleDenseRat 3 1
setup_fixed_benchmark runBareissDenseRatN3D1 where { carrierConfig with expectedHash := some 0x8e5a76cf61c17b9a }
setup_fixed_benchmark runOracleDenseRatN3D1 where oracleConfig
def runBareissDenseRatN3D2 := runBareissDenseRat 3 2
def runOracleDenseRatN3D2 := runOracleDenseRat 3 2
setup_fixed_benchmark runBareissDenseRatN3D2 where { carrierConfig with expectedHash := some 0xc25123dc84842f83 }
setup_fixed_benchmark runOracleDenseRatN3D2 where oracleConfig
def runBareissDenseRatN3D3 := runBareissDenseRat 3 3
def runOracleDenseRatN3D3 := runOracleDenseRat 3 3
setup_fixed_benchmark runBareissDenseRatN3D3 where { carrierConfig with expectedHash := some 0xc2e366c074fae226 }
setup_fixed_benchmark runOracleDenseRatN3D3 where oracleConfig
def runBareissDenseRatN4D1 := runBareissDenseRat 4 1
def runOracleDenseRatN4D1 := runOracleDenseRat 4 1
setup_fixed_benchmark runBareissDenseRatN4D1 where { carrierConfig with expectedHash := some 0x693fc516dab65368 }
setup_fixed_benchmark runOracleDenseRatN4D1 where oracleConfig
def runBareissDenseRatN4D2 := runBareissDenseRat 4 2
def runOracleDenseRatN4D2 := runOracleDenseRat 4 2
setup_fixed_benchmark runBareissDenseRatN4D2 where { carrierConfig with expectedHash := some 0xfc882c7039e56053 }
setup_fixed_benchmark runOracleDenseRatN4D2 where oracleConfig
def runBareissDenseRatN4D3 := runBareissDenseRat 4 3
def runOracleDenseRatN4D3 := runOracleDenseRat 4 3
setup_fixed_benchmark runBareissDenseRatN4D3 where { carrierConfig with expectedHash := some 0xce2e831909027d61 }
setup_fixed_benchmark runOracleDenseRatN4D3 where oracleConfig
def runBareissDenseRatN5D1 := runBareissDenseRat 5 1
def runOracleDenseRatN5D1 := runOracleDenseRat 5 1
setup_fixed_benchmark runBareissDenseRatN5D1 where { carrierConfig with expectedHash := some 0xc8e6d9c43aa94a0d }
setup_fixed_benchmark runOracleDenseRatN5D1 where oracleConfig
def runBareissDenseRatN5D2 := runBareissDenseRat 5 2
def runOracleDenseRatN5D2 := runOracleDenseRat 5 2
setup_fixed_benchmark runBareissDenseRatN5D2 where { carrierConfig with expectedHash := some 0x9667d9423c83931d }
setup_fixed_benchmark runOracleDenseRatN5D2 where oracleConfig
def runBareissDenseRatN5D3 := runBareissDenseRat 5 3
def runOracleDenseRatN5D3 := runOracleDenseRat 5 3
setup_fixed_benchmark runBareissDenseRatN5D3 where { carrierConfig with expectedHash := some 0xa2473f9af49c705f }
setup_fixed_benchmark runOracleDenseRatN5D3 where oracleConfig

def runBareissDenseMod (n degree : Nat) : Unit → IO String :=
  @hexCarrier (DensePoly Mod) _ _ _ _ _ _ DensePoly.instDecidableEq _
    n (denseEntry degree (2 : Mod)) (denseJson modJson)
def runOracleDenseMod (n degree : Nat) : Unit → IO String :=
  oracleCarrier "dense_mod" 1 n (denseEntry degree (2 : Mod)) (denseJson modJson)

def runBareissDenseModN3D1 := runBareissDenseMod 3 1
def runOracleDenseModN3D1 := runOracleDenseMod 3 1
setup_fixed_benchmark runBareissDenseModN3D1 where { carrierConfig with expectedHash := some 0x6d2f5c57370d6e0c }
setup_fixed_benchmark runOracleDenseModN3D1 where oracleConfig
def runBareissDenseModN3D2 := runBareissDenseMod 3 2
def runOracleDenseModN3D2 := runOracleDenseMod 3 2
setup_fixed_benchmark runBareissDenseModN3D2 where { carrierConfig with expectedHash := some 0x3b49b55d869b0ff5 }
setup_fixed_benchmark runOracleDenseModN3D2 where oracleConfig
def runBareissDenseModN3D3 := runBareissDenseMod 3 3
def runOracleDenseModN3D3 := runOracleDenseMod 3 3
setup_fixed_benchmark runBareissDenseModN3D3 where { carrierConfig with expectedHash := some 0xa01862690cbad9a7 }
setup_fixed_benchmark runOracleDenseModN3D3 where oracleConfig
def runBareissDenseModN4D1 := runBareissDenseMod 4 1
def runOracleDenseModN4D1 := runOracleDenseMod 4 1
setup_fixed_benchmark runBareissDenseModN4D1 where { carrierConfig with expectedHash := some 0x5e6bdfaf99352ab4 }
setup_fixed_benchmark runOracleDenseModN4D1 where oracleConfig
def runBareissDenseModN4D2 := runBareissDenseMod 4 2
def runOracleDenseModN4D2 := runOracleDenseMod 4 2
setup_fixed_benchmark runBareissDenseModN4D2 where { carrierConfig with expectedHash := some 0x9e3363f07db79551 }
setup_fixed_benchmark runOracleDenseModN4D2 where oracleConfig
def runBareissDenseModN4D3 := runBareissDenseMod 4 3
def runOracleDenseModN4D3 := runOracleDenseMod 4 3
setup_fixed_benchmark runBareissDenseModN4D3 where { carrierConfig with expectedHash := some 0xd7f0a898061fb609 }
setup_fixed_benchmark runOracleDenseModN4D3 where oracleConfig
def runBareissDenseModN5D1 := runBareissDenseMod 5 1
def runOracleDenseModN5D1 := runOracleDenseMod 5 1
setup_fixed_benchmark runBareissDenseModN5D1 where { carrierConfig with expectedHash := some 0x96ba65904ba6cf08 }
setup_fixed_benchmark runOracleDenseModN5D1 where oracleConfig
def runBareissDenseModN5D2 := runBareissDenseMod 5 2
def runOracleDenseModN5D2 := runOracleDenseMod 5 2
setup_fixed_benchmark runBareissDenseModN5D2 where { carrierConfig with expectedHash := some 0x7852839cac6c6217 }
setup_fixed_benchmark runOracleDenseModN5D2 where oracleConfig
def runBareissDenseModN5D3 := runBareissDenseMod 5 3
def runOracleDenseModN5D3 := runOracleDenseMod 5 3
setup_fixed_benchmark runBareissDenseModN5D3 where { carrierConfig with expectedHash := some 0x913f33b8567ef9f5 }
setup_fixed_benchmark runOracleDenseModN5D3 where oracleConfig

def runBareissZPoly (n degree : Nat) : Unit → IO String :=
  hexCarrier n (denseEntry degree (2 : Int)) (denseJson Lean.toJson)
def runOracleZPoly (n degree : Nat) : Unit → IO String :=
  oracleCarrier "zpoly" 1 n (denseEntry degree (2 : Int)) (denseJson Lean.toJson)

def runBareissZPolyN3D1 := runBareissZPoly 3 1
def runOracleZPolyN3D1 := runOracleZPoly 3 1
setup_fixed_benchmark runBareissZPolyN3D1 where { carrierConfig with expectedHash := some 0x6d2f5c57370d6e0c }
setup_fixed_benchmark runOracleZPolyN3D1 where oracleConfig
def runBareissZPolyN3D2 := runBareissZPoly 3 2
def runOracleZPolyN3D2 := runOracleZPoly 3 2
setup_fixed_benchmark runBareissZPolyN3D2 where { carrierConfig with expectedHash := some 0x3b49b55d869b0ff5 }
setup_fixed_benchmark runOracleZPolyN3D2 where oracleConfig
def runBareissZPolyN3D3 := runBareissZPoly 3 3
def runOracleZPolyN3D3 := runOracleZPoly 3 3
setup_fixed_benchmark runBareissZPolyN3D3 where { carrierConfig with expectedHash := some 0xa01862690cbad9a7 }
setup_fixed_benchmark runOracleZPolyN3D3 where oracleConfig
def runBareissZPolyN4D1 := runBareissZPoly 4 1
def runOracleZPolyN4D1 := runOracleZPoly 4 1
setup_fixed_benchmark runBareissZPolyN4D1 where { carrierConfig with expectedHash := some 0xfda799c9868d9ea2 }
setup_fixed_benchmark runOracleZPolyN4D1 where oracleConfig
def runBareissZPolyN4D2 := runBareissZPoly 4 2
def runOracleZPolyN4D2 := runOracleZPoly 4 2
setup_fixed_benchmark runBareissZPolyN4D2 where { carrierConfig with expectedHash := some 0x828899bfbe6372bc }
setup_fixed_benchmark runOracleZPolyN4D2 where oracleConfig
def runBareissZPolyN4D3 := runBareissZPoly 4 3
def runOracleZPolyN4D3 := runOracleZPoly 4 3
setup_fixed_benchmark runBareissZPolyN4D3 where { carrierConfig with expectedHash := some 0x8a3b30c3469614d5 }
setup_fixed_benchmark runOracleZPolyN4D3 where oracleConfig
def runBareissZPolyN5D1 := runBareissZPoly 5 1
def runOracleZPolyN5D1 := runOracleZPoly 5 1
setup_fixed_benchmark runBareissZPolyN5D1 where { carrierConfig with expectedHash := some 0xd2bd08a5126be42d }
setup_fixed_benchmark runOracleZPolyN5D1 where oracleConfig
def runBareissZPolyN5D2 := runBareissZPoly 5 2
def runOracleZPolyN5D2 := runOracleZPoly 5 2
setup_fixed_benchmark runBareissZPolyN5D2 where { carrierConfig with expectedHash := some 0x4f92439f3247680a }
setup_fixed_benchmark runOracleZPolyN5D2 where oracleConfig
def runBareissZPolyN5D3 := runBareissZPoly 5 3
def runOracleZPolyN5D3 := runOracleZPoly 5 3
setup_fixed_benchmark runBareissZPolyN5D3 where { carrierConfig with expectedHash := some 0x288e92aabd8fad6e }
setup_fixed_benchmark runOracleZPolyN5D3 where oracleConfig

def runBareissMvInt (n terms : Nat) : Unit → IO String :=
  hexCarrier n (mvEntry terms (2 : Int)) (mvJson Lean.toJson)
def runOracleMvInt (n terms : Nat) : Unit → IO String :=
  oracleCarrier "mv_int" 3 n (mvEntry terms (2 : Int)) (mvJson Lean.toJson)

def runBareissMvIntN3T2 := runBareissMvInt 3 2
def runOracleMvIntN3T2 := runOracleMvInt 3 2
setup_fixed_benchmark runBareissMvIntN3T2 where { carrierConfig with expectedHash := some 0x6ddf948aae3c92e7 }
setup_fixed_benchmark runOracleMvIntN3T2 where oracleConfig
def runBareissMvIntN3T3 := runBareissMvInt 3 3
def runOracleMvIntN3T3 := runOracleMvInt 3 3
setup_fixed_benchmark runBareissMvIntN3T3 where { carrierConfig with expectedHash := some 0xbdd0ae3db6b9a73b }
setup_fixed_benchmark runOracleMvIntN3T3 where oracleConfig
def runBareissMvIntN3T4 := runBareissMvInt 3 4
def runOracleMvIntN3T4 := runOracleMvInt 3 4
setup_fixed_benchmark runBareissMvIntN3T4 where { carrierConfig with expectedHash := some 0x9b59b471fa091466 }
setup_fixed_benchmark runOracleMvIntN3T4 where oracleConfig
def runBareissMvIntN4T2 := runBareissMvInt 4 2
def runOracleMvIntN4T2 := runOracleMvInt 4 2
setup_fixed_benchmark runBareissMvIntN4T2 where { carrierConfig with expectedHash := some 0x218e3309f71575fe }
setup_fixed_benchmark runOracleMvIntN4T2 where oracleConfig
def runBareissMvIntN4T3 := runBareissMvInt 4 3
def runOracleMvIntN4T3 := runOracleMvInt 4 3
setup_fixed_benchmark runBareissMvIntN4T3 where { carrierConfig with expectedHash := some 0x88e5d5424a4ff7f4 }
setup_fixed_benchmark runOracleMvIntN4T3 where oracleConfig
def runBareissMvIntN4T4 := runBareissMvInt 4 4
def runOracleMvIntN4T4 := runOracleMvInt 4 4
setup_fixed_benchmark runBareissMvIntN4T4 where { carrierConfig with expectedHash := some 0xac109eb5f191f9ef }
setup_fixed_benchmark runOracleMvIntN4T4 where oracleConfig
def runBareissMvIntN5T2 := runBareissMvInt 5 2
def runOracleMvIntN5T2 := runOracleMvInt 5 2
setup_fixed_benchmark runBareissMvIntN5T2 where { carrierConfig with expectedHash := some 0x4a93f54ed0f4bf15 }
setup_fixed_benchmark runOracleMvIntN5T2 where oracleConfig
def runBareissMvIntN5T3 := runBareissMvInt 5 3
def runOracleMvIntN5T3 := runOracleMvInt 5 3
setup_fixed_benchmark runBareissMvIntN5T3 where { carrierConfig with expectedHash := some 0x5c0c5a9098558fac }
setup_fixed_benchmark runOracleMvIntN5T3 where oracleConfig
def runBareissMvIntN5T4 := runBareissMvInt 5 4
def runOracleMvIntN5T4 := runOracleMvInt 5 4
setup_fixed_benchmark runBareissMvIntN5T4 where { carrierConfig with expectedHash := some 0xdbabfd0a0ac91e50 }
setup_fixed_benchmark runOracleMvIntN5T4 where oracleConfig

def runBareissMvRat (n terms : Nat) : Unit → IO String :=
  hexCarrier n (mvEntry terms (2 / 3 : Rat)) (mvJson ratJson)
def runOracleMvRat (n terms : Nat) : Unit → IO String :=
  oracleCarrier "mv_rat" 3 n (mvEntry terms (2 / 3 : Rat)) (mvJson ratJson)

def runBareissMvRatN3T2 := runBareissMvRat 3 2
def runOracleMvRatN3T2 := runOracleMvRat 3 2
setup_fixed_benchmark runBareissMvRatN3T2 where { carrierConfig with expectedHash := some 0x61c8648a3cf0b41f }
setup_fixed_benchmark runOracleMvRatN3T2 where oracleConfig
def runBareissMvRatN3T3 := runBareissMvRat 3 3
def runOracleMvRatN3T3 := runOracleMvRat 3 3
setup_fixed_benchmark runBareissMvRatN3T3 where { carrierConfig with expectedHash := some 0xa30b7647cce5d81d }
setup_fixed_benchmark runOracleMvRatN3T3 where oracleConfig
def runBareissMvRatN3T4 := runBareissMvRat 3 4
def runOracleMvRatN3T4 := runOracleMvRat 3 4
setup_fixed_benchmark runBareissMvRatN3T4 where { carrierConfig with expectedHash := some 0xc1afbd2597f98686 }
setup_fixed_benchmark runOracleMvRatN3T4 where oracleConfig
def runBareissMvRatN4T2 := runBareissMvRat 4 2
def runOracleMvRatN4T2 := runOracleMvRat 4 2
setup_fixed_benchmark runBareissMvRatN4T2 where { carrierConfig with expectedHash := some 0xc79deaae8255dba }
setup_fixed_benchmark runOracleMvRatN4T2 where oracleConfig
def runBareissMvRatN4T3 := runBareissMvRat 4 3
def runOracleMvRatN4T3 := runOracleMvRat 4 3
setup_fixed_benchmark runBareissMvRatN4T3 where { carrierConfig with expectedHash := some 0xd43a1b578d909614 }
setup_fixed_benchmark runOracleMvRatN4T3 where oracleConfig
def runBareissMvRatN4T4 := runBareissMvRat 4 4
def runOracleMvRatN4T4 := runOracleMvRat 4 4
setup_fixed_benchmark runBareissMvRatN4T4 where { carrierConfig with expectedHash := some 0x4bc36d60ed12ca14 }
setup_fixed_benchmark runOracleMvRatN4T4 where oracleConfig
def runBareissMvRatN5T2 := runBareissMvRat 5 2
def runOracleMvRatN5T2 := runOracleMvRat 5 2
setup_fixed_benchmark runBareissMvRatN5T2 where { carrierConfig with expectedHash := some 0x2fc4725b35a1c085 }
setup_fixed_benchmark runOracleMvRatN5T2 where oracleConfig
def runBareissMvRatN5T3 := runBareissMvRat 5 3
def runOracleMvRatN5T3 := runOracleMvRat 5 3
setup_fixed_benchmark runBareissMvRatN5T3 where { carrierConfig with expectedHash := some 0xbe366c20eccaacc3 }
setup_fixed_benchmark runOracleMvRatN5T3 where oracleConfig
def runBareissMvRatN5T4 := runBareissMvRat 5 4
def runOracleMvRatN5T4 := runOracleMvRat 5 4
setup_fixed_benchmark runBareissMvRatN5T4 where { carrierConfig with expectedHash := some 0x5bca1ea3a99f83b2 }
setup_fixed_benchmark runOracleMvRatN5T4 where oracleConfig


/-- Ordinary registration checks include all Hex carrier points. External carrier
comparisons are informational and run only when explicitly selected. -/
def verifyOrdinary : IO UInt32 := do
  let parametric ← LeanBench.allRuntimeEntries
  let fixed ← LeanBench.allFixedRuntimeEntries
  let names := ((parametric.filter fun e => !e.spec.config.tags.contains scheduledTag).map (·.spec.name)).toList ++
    ((fixed.filter fun e => !e.spec.config.tags.contains scheduledTag).map (·.spec.name)).toList
  let reports ← LeanBench.verify names
  IO.println (LeanBench.Format.fmtCombinedVerify reports)
  return if reports.passed then 0 else 1

end Hex.BareissBench

def main (args : List String) : IO UInt32 :=
  match args with
  | ["verify"] => Hex.BareissBench.verifyOrdinary
  | _ => LeanBench.Cli.dispatch args
