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

def runOp (family op : String) (fields : Array (String × Json)) : IO Json := do
  let mut object : Array (String × Json) :=
    #[("family", Json.str family), ("op", Json.str op)]
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

private def expectTrue (context : String) (result : Json) : IO Unit := do
  unless (← jsonError s!"{context} result is not a boolean" result.getBool?) do
    throw <| IO.userError s!"{context} request returned false"

def intGcd {n : Nat} (input : Flint.P n Int × Flint.P n Int)
    (expected : Flint.P n Int) : IO Flint.IntTerms := do
  let result ← runOp "integer_mpoly" "gcd_equals" #[
    ("nvars", Json.num (Lean.JsonNumber.fromNat n)),
    ("a", Flint.intTermsJson input.1), ("b", Flint.intTermsJson input.2),
    ("expected", Flint.intTermsJson expected)]
  expectTrue "Singular GCD" result
  return Flint.intTerms expected

def ratGcd {n : Nat} (input : Flint.P n Rat × Flint.P n Rat)
    (expected : Flint.P n Rat) : IO Flint.RatTerms := do
  let result ← runOp "rational_mpoly" "gcd_equals" #[
    ("nvars", Json.num (Lean.JsonNumber.fromNat n)),
    ("a", Flint.ratTermsJson input.1), ("b", Flint.ratTermsJson input.2),
    ("expected", Flint.ratTermsJson expected)]
  expectTrue "Singular rational GCD" result
  return Flint.ratTerms expected

def intDiv {n : Nat} (dividend divisor expected : Flint.P n Int) :
    IO Flint.IntTerms := do
  let result ← runOp "integer_mpoly" "div_equals" #[
    ("nvars", Json.num (Lean.JsonNumber.fromNat n)),
    ("a", Flint.intTermsJson dividend), ("b", Flint.intTermsJson divisor),
    ("expected", Flint.intTermsJson expected)]
  expectTrue "Singular exact division" result
  return Flint.intTerms expected

def intSquarefree {n : Nat} (polynomial : Flint.P n Int) : IO (List Nat) := do
  let result ← runOp "integer_mpoly" "squarefree" #[
    ("nvars", Json.num (Lean.JsonNumber.fromNat n)),
    ("a", Flint.intTermsJson polynomial)]
  let values ← jsonError "Singular squarefree result is not an array" result.getArr?
  values.toList.mapM fun value =>
    jsonError "Singular squarefree multiplicity is not a natural" value.getNat?

def runOverhead (_ : Unit) : IO (List (List Nat × Int)) := do
  let result ← runOp "integer_mpoly" "overhead" #[]
  expectTrue "Singular overhead" result
  return []

def runCoprime2 (_ : Unit) : IO (List (List Nat × Int)) := do
  let input ← Flint.coprime1.get
  let result ← runOp "integer_mpoly" "gcd_is_one" #[
    ("nvars", Json.num (Lean.JsonNumber.fromNat 2)),
    ("a", Flint.intTermsJson input.left), ("b", Flint.intTermsJson input.right)]
  expectTrue "Singular coprime" result
  return [([0, 0], 1)]

def config (expectedHash : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 12.0, minTotalSeconds := 0.2,
    warmupFirstIter := true, expectedHash := some expectedHash }

end Hex.MvGcdBench.Singular
