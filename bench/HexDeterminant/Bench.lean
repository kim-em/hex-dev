/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDeterminant
import HexDeterminant.Carriers
import Hex.BenchOracle.Flint
import LeanBench

/-!
Benchmark registrations for `hex-determinant`.

This Phase 4 slice measures the generic Leibniz-formula determinant on small
deterministically generated integer inputs. Matrix construction is hoisted into
`prep` so the declared model tracks the timed algebraic operation rather than
fixture construction.

Scientific registration:

* `runLeibnizDet`: generic Leibniz determinant, `O(n * n!)`, capped at small
  dimensions where the factorial permutation sum remains practical.

The integer `runLeibnizDet` target has no external comparator: it is the reference
combinatorial definition, cross-checked against the row-pivoted Bareiss
determinant (`hex-bareiss`) for agreement rather than against an external tool
(declared absence with the `structural-layer` reason per
`SPEC/Libraries/hex-determinant.md §"External comparators"`).
-/

namespace Hex.DeterminantBench

/-- Flattened benchmark input for one square integer matrix. -/
structure DetInput where
  n : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

/-- Deterministic tridiagonal entries for determinant benchmarks. The shape
keeps intermediates small so the registration tests the permutation-sum scaling
rather than arbitrary-precision integer growth in random minors. -/
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

/-- Textbook operation-count model for the generic Leibniz determinant path:
the signed sum over all `n!` permutations, each an `n`-fold product. -/
def leibnizDetComplexity : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * leibnizDetComplexity n

/-- Benchmark target: compute the determinant using the generic Leibniz
definition. Capped at small dimensions where the factorial sum is practical. -/
def runLeibnizDet (input : DetInput) : Int :=
  let M : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.entries
  Hex.Matrix.det M

/-! `runLeibnizDet` cost model: the Leibniz determinant is the signed sum over
`n!` permutations of an `n`-fold diagonal product, so the operation count is
`n * n!`, i.e. `n * leibnizDetComplexity n`. -/
setup_benchmark runLeibnizDet n => n * leibnizDetComplexity n
  with prep := prepDetInput
  where {
    paramFloor := 2
    paramCeiling := 8
    paramSchedule := .custom #[2, 3, 4, 5, 6, 7, 8]
    maxSecondsPerCall := 1.5
    targetInnerNanos := 800000000
    verdictWarmupFraction := 0.5
  }


/-! Symbolic carrier sweeps. Each fixed point compares the full canonical
result on a prepared input. Dimensions are 2, 3, 4; dense and fraction degrees
are 1, 2, 4; multivariate term counts are 2, 4, 8 at arity 3 and total degree 4.
The SymPy points are informational, scheduled-only, and excluded from bare
`verify`. Explicit names still verify the external process and result hashes. -/

open DeterminantCarriers
open scoped Hex.DeterminantCarriers

initialize carrierDriver : IO.Ref (Option Hex.BenchOracle.Flint.PersistentComparator) ← IO.mkRef none

/-- Start one SymPy process per benchmark child and reuse it within the batch. -/
def carrierLine (line : String) : IO String := do
  let child ← match ← carrierDriver.get with
    | some child => pure child
    | none => do
      let python := (← IO.getEnv "HEX_MATRIX_CARRIERS_PYTHON").getD "python3"
      let rootPath : System.FilePath := "scripts/oracle/matrix_carriers_bench_driver.py"
      let defaultPath ← if ← rootPath.pathExists then pure rootPath.toString
        else pure s!"../{rootPath}"
      let path := (← IO.getEnv "HEX_MATRIX_CARRIERS_DRIVER").getD defaultPath
      if !(← (System.FilePath.mk path).pathExists) then
        throw <| IO.userError s!"carrier driver not found: {path}; set HEX_MATRIX_CARRIERS_DRIVER"
      let child ← Hex.BenchOracle.Flint.PersistentComparator.spawn python #[path]
      carrierDriver.set (some child)
      pure child
  -- Preserve a failed measurement, but let a later request start a new child.
  let response ← try child.requestLine line catch error =>
    carrierDriver.set none
    throw error
  let json ← IO.ofExcept (Lean.Json.parse response)
  if (json.getObjValAs? Bool "ok").toOption != some true then
    throw <| IO.userError s!"carrier comparator failed: {response}"
  let result ← IO.ofExcept (json.getObjVal? "result")
  return result.compress

/-- Matrix preparation is outside the returned timed closure. -/
def detAt [Lean.Grind.Ring R] (encode : R → Lean.Json)
    (entry : Nat → Nat → Nat → R) (n size : Nat) : Unit → IO String :=
  let M := DeterminantCarriers.matrix entry n size
  fun _ => pure ((encode (Matrix.det M)).compress)

/-- The first warmup request prepares the identical matrix in the Python driver. -/
def sympyAt (domain : Domain) (encode : R → Lean.Json)
    (entry : Nat → Nat → Nat → R) (n size : Nat) : Unit → IO String :=
  let M := DeterminantCarriers.matrix entry n size
  let line := (request domain encode M).compress
  fun _ => carrierLine line

def scheduledOnlyTag : String := "scheduled-only"

def carrierConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, minTotalSeconds := 0.2, maxSecondsPerCall := 10.0,
    warmupFirstIter := true, tags := #["det-carrier"] }

def sympyConfig : LeanBench.FixedBenchmarkConfig :=
  { carrierConfig with tags := #["det-carrier", scheduledOnlyTag] }

def runCarrierOverhead (_ : Unit) : IO String :=
  carrierLine "{\"kind\":\"overhead\"}"

setup_fixed_benchmark runCarrierOverhead where { sympyConfig with expectedHash := some 0xa00b9350ae2c0b96 }

def runDetDenseInt (n degree : Nat) : Unit → IO String :=
  detAt (polyJson Lean.toJson) intPoly n degree

def runSympyDenseInt (n degree : Nat) : Unit → IO String :=
  sympyAt (denseInt) (polyJson Lean.toJson) intPoly n degree

def runDetDenseInt_2_2 := runDetDenseInt 2 2
def runSympyDenseInt_2_2 := runSympyDenseInt 2 2
setup_fixed_benchmark runDetDenseInt_2_2 where { carrierConfig with expectedHash := some 0x24c80a80914a323 }
setup_fixed_benchmark runSympyDenseInt_2_2 where { sympyConfig with expectedHash := some 0x24c80a80914a323 }

def runDetDenseInt_3_2 := runDetDenseInt 3 2
def runSympyDenseInt_3_2 := runSympyDenseInt 3 2
setup_fixed_benchmark runDetDenseInt_3_2 where { carrierConfig with expectedHash := some 0x768691c749a3b9fb }
setup_fixed_benchmark runSympyDenseInt_3_2 where { sympyConfig with expectedHash := some 0x768691c749a3b9fb }

def runDetDenseInt_4_2 := runDetDenseInt 4 2
def runSympyDenseInt_4_2 := runSympyDenseInt 4 2
setup_fixed_benchmark runDetDenseInt_4_2 where { carrierConfig with expectedHash := some 0xd9adb7d015389ef8 }
setup_fixed_benchmark runSympyDenseInt_4_2 where { sympyConfig with expectedHash := some 0xd9adb7d015389ef8 }

def runDetDenseInt_3_1 := runDetDenseInt 3 1
def runSympyDenseInt_3_1 := runSympyDenseInt 3 1
setup_fixed_benchmark runDetDenseInt_3_1 where { carrierConfig with expectedHash := some 0xe5f12eee41c0b7f5 }
setup_fixed_benchmark runSympyDenseInt_3_1 where { sympyConfig with expectedHash := some 0xe5f12eee41c0b7f5 }

def runDetDenseInt_3_4 := runDetDenseInt 3 4
def runSympyDenseInt_3_4 := runSympyDenseInt 3 4
setup_fixed_benchmark runDetDenseInt_3_4 where { carrierConfig with expectedHash := some 0xa2d3366b9d8c1da4 }
setup_fixed_benchmark runSympyDenseInt_3_4 where { sympyConfig with expectedHash := some 0xa2d3366b9d8c1da4 }

def runDetDenseRat (n degree : Nat) : Unit → IO String :=
  detAt (polyJson ratJson) ratPoly n degree

def runSympyDenseRat (n degree : Nat) : Unit → IO String :=
  sympyAt (denseRat) (polyJson ratJson) ratPoly n degree

def runDetDenseRat_2_2 := runDetDenseRat 2 2
def runSympyDenseRat_2_2 := runSympyDenseRat 2 2
setup_fixed_benchmark runDetDenseRat_2_2 where { carrierConfig with expectedHash := some 0x3e6f65769e12e2b }
setup_fixed_benchmark runSympyDenseRat_2_2 where { sympyConfig with expectedHash := some 0x3e6f65769e12e2b }

def runDetDenseRat_3_2 := runDetDenseRat 3 2
def runSympyDenseRat_3_2 := runSympyDenseRat 3 2
setup_fixed_benchmark runDetDenseRat_3_2 where { carrierConfig with expectedHash := some 0xa49ffb0adb08e7a }
setup_fixed_benchmark runSympyDenseRat_3_2 where { sympyConfig with expectedHash := some 0xa49ffb0adb08e7a }

def runDetDenseRat_4_2 := runDetDenseRat 4 2
def runSympyDenseRat_4_2 := runSympyDenseRat 4 2
setup_fixed_benchmark runDetDenseRat_4_2 where { carrierConfig with expectedHash := some 0xb01653837fa89fae }
setup_fixed_benchmark runSympyDenseRat_4_2 where { sympyConfig with expectedHash := some 0xb01653837fa89fae }

def runDetDenseRat_3_1 := runDetDenseRat 3 1
def runSympyDenseRat_3_1 := runSympyDenseRat 3 1
setup_fixed_benchmark runDetDenseRat_3_1 where { carrierConfig with expectedHash := some 0xb9644eec3e525d6 }
setup_fixed_benchmark runSympyDenseRat_3_1 where { sympyConfig with expectedHash := some 0xb9644eec3e525d6 }

def runDetDenseRat_3_4 := runDetDenseRat 3 4
def runSympyDenseRat_3_4 := runSympyDenseRat 3 4
setup_fixed_benchmark runDetDenseRat_3_4 where { carrierConfig with expectedHash := some 0xb9b62dec355cc3be }
setup_fixed_benchmark runSympyDenseRat_3_4 where { sympyConfig with expectedHash := some 0xb9b62dec355cc3be }

def runDetDenseMod (n degree : Nat) : Unit → IO String :=
  detAt (polyJson (fun c : Mod => Lean.toJson c.toNat)) modPoly n degree

def runSympyDenseMod (n degree : Nat) : Unit → IO String :=
  sympyAt (denseMod) (polyJson (fun c : Mod => Lean.toJson c.toNat)) modPoly n degree

def runDetDenseMod_2_2 := runDetDenseMod 2 2
def runSympyDenseMod_2_2 := runSympyDenseMod 2 2
setup_fixed_benchmark runDetDenseMod_2_2 where { carrierConfig with expectedHash := some 0x215899477db6d9f2 }
setup_fixed_benchmark runSympyDenseMod_2_2 where { sympyConfig with expectedHash := some 0x215899477db6d9f2 }

def runDetDenseMod_3_2 := runDetDenseMod 3 2
def runSympyDenseMod_3_2 := runSympyDenseMod 3 2
setup_fixed_benchmark runDetDenseMod_3_2 where { carrierConfig with expectedHash := some 0x56868dfc2e733eb9 }
setup_fixed_benchmark runSympyDenseMod_3_2 where { sympyConfig with expectedHash := some 0x56868dfc2e733eb9 }

def runDetDenseMod_4_2 := runDetDenseMod 4 2
def runSympyDenseMod_4_2 := runSympyDenseMod 4 2
setup_fixed_benchmark runDetDenseMod_4_2 where { carrierConfig with expectedHash := some 0xc4dd2e0f8a08e917 }
setup_fixed_benchmark runSympyDenseMod_4_2 where { sympyConfig with expectedHash := some 0xc4dd2e0f8a08e917 }

def runDetDenseMod_3_1 := runDetDenseMod 3 1
def runSympyDenseMod_3_1 := runSympyDenseMod 3 1
setup_fixed_benchmark runDetDenseMod_3_1 where { carrierConfig with expectedHash := some 0x9282de3db12b5009 }
setup_fixed_benchmark runSympyDenseMod_3_1 where { sympyConfig with expectedHash := some 0x9282de3db12b5009 }

def runDetDenseMod_3_4 := runDetDenseMod 3 4
def runSympyDenseMod_3_4 := runSympyDenseMod 3 4
setup_fixed_benchmark runDetDenseMod_3_4 where { carrierConfig with expectedHash := some 0x5c20a327d83aa660 }
setup_fixed_benchmark runSympyDenseMod_3_4 where { sympyConfig with expectedHash := some 0x5c20a327d83aa660 }

def runDetMvInt (n terms : Nat) : Unit → IO String :=
  detAt (mvJson Lean.toJson) intMv n terms

def runSympyMvInt (n terms : Nat) : Unit → IO String :=
  sympyAt (mvInt 3) (mvJson Lean.toJson) intMv n terms

def runDetMvInt_2_4 := runDetMvInt 2 4
def runSympyMvInt_2_4 := runSympyMvInt 2 4
setup_fixed_benchmark runDetMvInt_2_4 where { carrierConfig with expectedHash := some 0x756f934820dc2e47 }
setup_fixed_benchmark runSympyMvInt_2_4 where { sympyConfig with expectedHash := some 0x756f934820dc2e47 }

def runDetMvInt_3_4 := runDetMvInt 3 4
def runSympyMvInt_3_4 := runSympyMvInt 3 4
setup_fixed_benchmark runDetMvInt_3_4 where { carrierConfig with expectedHash := some 0x60bf11fb309e6a7f }
setup_fixed_benchmark runSympyMvInt_3_4 where { sympyConfig with expectedHash := some 0x60bf11fb309e6a7f }

def runDetMvInt_4_4 := runDetMvInt 4 4
def runSympyMvInt_4_4 := runSympyMvInt 4 4
setup_fixed_benchmark runDetMvInt_4_4 where { carrierConfig with expectedHash := some 0xe7fc565164275455 }
setup_fixed_benchmark runSympyMvInt_4_4 where { sympyConfig with expectedHash := some 0xe7fc565164275455 }

def runDetMvInt_3_2 := runDetMvInt 3 2
def runSympyMvInt_3_2 := runSympyMvInt 3 2
setup_fixed_benchmark runDetMvInt_3_2 where { carrierConfig with expectedHash := some 0x93a3482331a5b88f }
setup_fixed_benchmark runSympyMvInt_3_2 where { sympyConfig with expectedHash := some 0x93a3482331a5b88f }

def runDetMvInt_3_8 := runDetMvInt 3 8
def runSympyMvInt_3_8 := runSympyMvInt 3 8
setup_fixed_benchmark runDetMvInt_3_8 where { carrierConfig with expectedHash := some 0xa3d95b0ee0f711eb }
setup_fixed_benchmark runSympyMvInt_3_8 where { sympyConfig with expectedHash := some 0xa3d95b0ee0f711eb }

def runDetMvRat (n terms : Nat) : Unit → IO String :=
  detAt (mvJson ratJson) ratMv n terms

def runSympyMvRat (n terms : Nat) : Unit → IO String :=
  sympyAt (mvRat 3) (mvJson ratJson) ratMv n terms

def runDetMvRat_2_4 := runDetMvRat 2 4
def runSympyMvRat_2_4 := runSympyMvRat 2 4
setup_fixed_benchmark runDetMvRat_2_4 where { carrierConfig with expectedHash := some 0x6864782c7412207f }
setup_fixed_benchmark runSympyMvRat_2_4 where { sympyConfig with expectedHash := some 0x6864782c7412207f }

def runDetMvRat_3_4 := runDetMvRat 3 4
def runSympyMvRat_3_4 := runSympyMvRat 3 4
setup_fixed_benchmark runDetMvRat_3_4 where { carrierConfig with expectedHash := some 0xcb8f96dd2fb52a2c }
setup_fixed_benchmark runSympyMvRat_3_4 where { sympyConfig with expectedHash := some 0xcb8f96dd2fb52a2c }

def runDetMvRat_4_4 := runDetMvRat 4 4
def runSympyMvRat_4_4 := runSympyMvRat 4 4
setup_fixed_benchmark runDetMvRat_4_4 where { carrierConfig with expectedHash := some 0x2c818b2dd0f38767 }
setup_fixed_benchmark runSympyMvRat_4_4 where { sympyConfig with expectedHash := some 0x2c818b2dd0f38767 }

def runDetMvRat_3_2 := runDetMvRat 3 2
def runSympyMvRat_3_2 := runSympyMvRat 3 2
setup_fixed_benchmark runDetMvRat_3_2 where { carrierConfig with expectedHash := some 0x23f2a5da0aacc415 }
setup_fixed_benchmark runSympyMvRat_3_2 where { sympyConfig with expectedHash := some 0x23f2a5da0aacc415 }

def runDetMvRat_3_8 := runDetMvRat 3 8
def runSympyMvRat_3_8 := runSympyMvRat 3 8
setup_fixed_benchmark runDetMvRat_3_8 where { carrierConfig with expectedHash := some 0x36952302bcd7b916 }
setup_fixed_benchmark runSympyMvRat_3_8 where { sympyConfig with expectedHash := some 0x36952302bcd7b916 }

def runDetRatFn (n degree : Nat) : Unit → IO String :=
  detAt (fractionJson) fraction n degree

def runSympyRatFn (n degree : Nat) : Unit → IO String :=
  sympyAt (ratFn) (fractionJson) fraction n degree

def runDetRatFn_2_2 := runDetRatFn 2 2
def runSympyRatFn_2_2 := runSympyRatFn 2 2
setup_fixed_benchmark runDetRatFn_2_2 where { carrierConfig with expectedHash := some 0xfcff0e0a7ff7e4d5 }
setup_fixed_benchmark runSympyRatFn_2_2 where { sympyConfig with expectedHash := some 0xfcff0e0a7ff7e4d5 }

def runDetRatFn_3_2 := runDetRatFn 3 2
def runSympyRatFn_3_2 := runSympyRatFn 3 2
setup_fixed_benchmark runDetRatFn_3_2 where { carrierConfig with expectedHash := some 0xe2a7a4ce25e58bb }
setup_fixed_benchmark runSympyRatFn_3_2 where { sympyConfig with expectedHash := some 0xe2a7a4ce25e58bb }

def runDetRatFn_4_2 := runDetRatFn 4 2
def runSympyRatFn_4_2 := runSympyRatFn 4 2
setup_fixed_benchmark runDetRatFn_4_2 where { carrierConfig with expectedHash := some 0x42ebb5b65f6ad59b }
setup_fixed_benchmark runSympyRatFn_4_2 where { sympyConfig with expectedHash := some 0x42ebb5b65f6ad59b }

def runDetRatFn_3_1 := runDetRatFn 3 1
def runSympyRatFn_3_1 := runSympyRatFn 3 1
setup_fixed_benchmark runDetRatFn_3_1 where { carrierConfig with expectedHash := some 0x415775e825d44d56 }
setup_fixed_benchmark runSympyRatFn_3_1 where { sympyConfig with expectedHash := some 0x415775e825d44d56 }

def runDetRatFn_3_4 := runDetRatFn 3 4
def runSympyRatFn_3_4 := runSympyRatFn 3 4
setup_fixed_benchmark runDetRatFn_3_4 where { carrierConfig with expectedHash := some 0xb2e3fa491f5e2fe5 }
setup_fixed_benchmark runSympyRatFn_3_4 where { sympyConfig with expectedHash := some 0xb2e3fa491f5e2fe5 }

/-- Default CI verifies every Lean carrier rung without launching SymPy. -/
def verifyCarriers : IO UInt32 := do
  let parametric ← LeanBench.allRuntimeEntries
  let fixed ← LeanBench.allFixedRuntimeEntries
  let names :=
    (parametric.filter (fun e => !e.spec.config.tags.contains scheduledOnlyTag)
      |>.map (·.spec.name) |>.toList) ++
    (fixed.filter (fun e => !e.spec.config.tags.contains scheduledOnlyTag)
      |>.map (·.spec.name) |>.toList)
  let reports ← LeanBench.verify names
  IO.println (LeanBench.Format.fmtCombinedVerify reports)
  return if reports.passed then 0 else 1

end Hex.DeterminantBench

def main (args : List String) : IO UInt32 :=
  match args with
  | ["verify"] => Hex.DeterminantBench.verifyCarriers
  | _ => LeanBench.Cli.dispatch args
