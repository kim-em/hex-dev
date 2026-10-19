/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSturm
import LeanBench
import Hex.BenchOracle.Flint

/-! Informational complete-query comparators on `T_8` and (-2,2).
Coefficient inputs and backend contexts are prepared; every request invokes
root production, open-interval filtering, exact query evaluation and sign sum.
JSON transport and temporary cleanup remain timed. The persistent drivers
cache no roots; external backends may retain internal caches. These fixed
endpoints and protocol controls make no complexity or absolute-budget claim.
They do not compare literal certificates or isolate root production as a query.
-/
namespace Hex.SturmExternalBench
open Hex DensePoly

initialize inputs : IO.Ref (Array (DensePoly Rat)) ← do
  let p : DensePoly Rat := ofCoeffs #[1, 0, -32, 0, 160, 0, -256, 0, 128]
  IO.mkRef #[p, 1, ofCoeffs #[0, 1], ofCoeffs #[-1, 1], p]

private def nativeQuery (fixture : Nat) : IO (Option Int) := do
  let polynomials ← inputs.get
  let some p := polynomials[0]? | throw (IO.userError "missing fixed head")
  let some q := polynomials[fixture + 1]? | throw (IO.userError "unknown fixed query")
  return Sturm.query Sturm.orderSign p q (.finite (-2)) (.finite 2)

initialize flintRef : IO.Ref (Option Hex.BenchOracle.Flint.PersistentComparator) ← IO.mkRef none
initialize z3Ref : IO.Ref (Option Hex.BenchOracle.Flint.PersistentComparator) ← IO.mkRef none

private def oracleQuery (tool fixture : String) (control := false) : IO (Option Int) := do
  let ref := if tool == "flint" then flintRef else z3Ref
  let driver ← match (← ref.get) with
    | some driver => pure driver
    | none => do
      let python := (← IO.getEnv "HEX_FLINT_BENCH_PYTHON").getD "python3"
      let path : System.FilePath := "scripts/oracle/sturm_bench.py"
      let script := if (← path.pathExists) then path.toString
        else "../scripts/oracle/sturm_bench.py"
      let driver ← Hex.BenchOracle.Flint.PersistentComparator.spawn python #[script, "--tool", tool]
      ref.set (some driver)
      pure driver
  let reply ← driver.requestLine (Lean.Json.mkObj
    [("case", Lean.toJson fixture), ("control", Lean.toJson control)]).compress
  let parsed ← IO.ofExcept (Lean.Json.parse reply)
  unless (← IO.ofExcept (parsed.getObjValAs? Bool "ok")) do
    throw (IO.userError s!"exact {tool} query failed: {reply}")
  return some (← IO.ofExcept (parsed.getObjValAs? Int "result"))

private def observations : LeanBench.FixedBenchmarkConfig := {
  repeats := 4
  maxSecondsPerCall := 30
  warmupFirstIter := true
}

def runNativeCount : Unit → IO (Option Int) := fun _ => nativeQuery 0
def runFlintCount : Unit → IO (Option Int) := fun _ => oracleQuery "flint" "count"
def runZ3Count : Unit → IO (Option Int) := fun _ => oracleQuery "z3" "count"

-- Fixed complete-query and expected-result anchors; informational comparison, no mode.
setup_fixed_benchmark runNativeCount where { observations with expectedHash := some (hash (some (8 : Int))) }
setup_fixed_benchmark runFlintCount where { observations with expectedHash := some (hash (some (8 : Int))) }
setup_fixed_benchmark runZ3Count where { observations with expectedHash := some (hash (some (8 : Int))) }

def runNativeMixed : Unit → IO (Option Int) := fun _ => nativeQuery 1
def runFlintMixed : Unit → IO (Option Int) := fun _ => oracleQuery "flint" "mixed"
def runZ3Mixed : Unit → IO (Option Int) := fun _ => oracleQuery "z3" "mixed"

-- Fixed complete-query and expected-result anchors; informational comparison, no mode.
setup_fixed_benchmark runNativeMixed where { observations with expectedHash := some (hash (some (0 : Int))) }
setup_fixed_benchmark runFlintMixed where { observations with expectedHash := some (hash (some (0 : Int))) }
setup_fixed_benchmark runZ3Mixed where { observations with expectedHash := some (hash (some (0 : Int))) }

def runNativeNegative : Unit → IO (Option Int) := fun _ => nativeQuery 2
def runFlintNegative : Unit → IO (Option Int) := fun _ => oracleQuery "flint" "negative"
def runZ3Negative : Unit → IO (Option Int) := fun _ => oracleQuery "z3" "negative"

-- Fixed complete-query and expected-result anchors; informational comparison, no mode.
setup_fixed_benchmark runNativeNegative where { observations with expectedHash := some (hash (some (-8 : Int))) }
setup_fixed_benchmark runFlintNegative where { observations with expectedHash := some (hash (some (-8 : Int))) }
setup_fixed_benchmark runZ3Negative where { observations with expectedHash := some (hash (some (-8 : Int))) }

def runNativeCommon : Unit → IO (Option Int) := fun _ => nativeQuery 3
def runFlintCommon : Unit → IO (Option Int) := fun _ => oracleQuery "flint" "common"
def runZ3Common : Unit → IO (Option Int) := fun _ => oracleQuery "z3" "common"

-- Fixed complete-query and expected-result anchors; informational comparison, no mode.
setup_fixed_benchmark runNativeCommon where { observations with expectedHash := some (hash (some (0 : Int))) }
setup_fixed_benchmark runFlintCommon where { observations with expectedHash := some (hash (some (0 : Int))) }
setup_fixed_benchmark runZ3Common where { observations with expectedHash := some (hash (some (0 : Int))) }

def runFlintProtocol : Unit → IO (Option Int) := fun _ => oracleQuery "flint" "count" true

-- Protocol-overhead control with the complete count payload; no mode or performance budget.
setup_fixed_benchmark runFlintProtocol where { observations with expectedHash := some (hash (some (8 : Int))) }

def runZ3Protocol : Unit → IO (Option Int) := fun _ => oracleQuery "z3" "count" true

-- Protocol-overhead control with the complete count payload; no mode or performance budget.
setup_fixed_benchmark runZ3Protocol where { observations with expectedHash := some (hash (some (8 : Int))) }

end Hex.SturmExternalBench
