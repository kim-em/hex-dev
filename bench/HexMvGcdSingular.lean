/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.BenchOracle.Flint
import HexMvGcdFlint
import LeanBench

/-!
Singular's like-for-like coprime multivariate-GCD comparator.

The persistent Python service keeps Singular itself alive across an autotuned
child batch.  Singular certifies that the fixed integer pair has unit GCD over
the rational polynomial ring; the Lean registration returns the same canonical
constant polynomial, so LeanBench comparison still checks exact agreement.
-/

namespace Hex.MvGcdBench.Singular

open Hex.MvPoly
open Lean (Json)

private abbrev PersistentComparator :=
  Hex.BenchOracle.Flint.PersistentComparator

initialize driverRef : IO.Ref (Option PersistentComparator) ← IO.mkRef none

private def envOr (name default : String) : IO String := do
  return (← IO.getEnv name).getD default

private def driverPath : IO String := do
  if let some path ← IO.getEnv "HEX_SINGULAR_BENCH_DRIVER" then
    return path
  let root : System.FilePath := "scripts/oracle/singular_bench_driver.py"
  if ← root.pathExists then return root.toString
  return "../scripts/oracle/singular_bench_driver.py"

private def resolveDriver : IO PersistentComparator := do
  if let some child ← driverRef.get then return child
  let child ← Hex.BenchOracle.Flint.PersistentComparator.spawn
    (← envOr "HEX_SINGULAR_BENCH_PYTHON" "python3") #[← driverPath]
  driverRef.set (some child)
  return child

private def jsonError (context : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"{context}: {error}"

private def runOp (op : String) (fields : Array (String × Json)) : IO Json := do
  let mut object : Array (String × Json) :=
    #[("family", Json.str "integer_mpoly"), ("op", Json.str op)]
  for field in fields do object := object.push field
  let replyLine ← Hex.BenchOracle.Flint.PersistentComparator.requestLine
    (← resolveDriver) (Json.mkObj object.toList).compress
  let reply ← match Json.parse replyLine with
    | Except.ok value => pure value
    | Except.error error => throw (IO.userError
        s!"singular_bench_driver reply not valid JSON: {error}; reply: {replyLine}")
  match reply.getObjValAs? Bool "ok" with
  | Except.ok true =>
      match reply.getObjVal? "result" with
      | Except.ok result => return result
      | Except.error error => throw (IO.userError
          s!"singular_bench_driver missing result: {error}")
  | Except.ok false =>
      let error := (reply.getObjValAs? String "error").toOption.getD
        "(no error message)"
      throw <| IO.userError s!"singular_bench_driver: {error}"
  | Except.error error => throw (IO.userError
      s!"singular_bench_driver missing/non-bool ok: {error}")

private def termsJson (p : Flint.P2 Int) : Json :=
  Json.arr <| (p.termsList.map fun term =>
    Json.arr #[
      Json.arr (term.1.toList.map (fun exponent =>
        Json.num (Lean.JsonNumber.fromNat exponent))).toArray,
      Json.num (Lean.JsonNumber.fromInt term.2)]).toArray

def runOverhead (_ : Unit) : IO (List (List Nat × Int)) := do
  let result ← runOp "overhead" #[]
  unless (← jsonError "Singular overhead result is not a boolean" result.getBool?) do
    throw <| IO.userError "Singular overhead request returned false"
  return []

def runCoprime2 (_ : Unit) : IO (List (List Nat × Int)) := do
  let input ← Flint.coprime1.get
  let result ← runOp "gcd_is_one" #[
    ("nvars", Json.num (Lean.JsonNumber.fromNat 2)),
    ("a", termsJson input.left), ("b", termsJson input.right)]
  unless (← jsonError "Singular coprime result is not a boolean" result.getBool?) do
    throw <| IO.userError "Singular coprime request returned false"
  return [([0, 0], 1)]

def config (expectedHash : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 12.0, minTotalSeconds := 0.2,
    warmupFirstIter := true, expectedHash := some expectedHash }

end Hex.MvGcdBench.Singular
