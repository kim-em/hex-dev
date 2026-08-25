/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.BenchOracle.Flint
import HexMvGcd
import LeanBench

/-!
FLINT comparison fixtures for `hex-mv-gcd`.

The Lean and FLINT registrations return the same canonical sparse term list,
so LeanBench's `compare` command checks correctness as well as reporting the
timings. Input construction and JSON translation are outside the gcd kernels,
and the separate overhead registration measures the persistent driver's
steady-state framing cost.
-/

namespace Hex.MvGcdBench.Flint

open Hex
open Hex.MvPoly

abbrev P2 (R : Type) [Zero R] := MvPoly 2 R Mono.lex

structure CoprimeInput where
  left : P2 Int
  right : P2 Int
  deriving Nonempty

/-- A deterministic coprime pair for cross-system comparison. -/
def prepCoprime (degree : Nat) : CoprimeInput :=
  let x : P2 Int := X 0
  let y : P2 Int := X 1
  { left := x ^ (degree + 1) + y + 1
    right := y ^ (degree + 1) + x + 2 }

private def terms (p : P2 Int) : List (List Nat × Int) :=
  p.termsList.map fun term => (term.1.toList, term.2)

private def termsJson (p : P2 Int) : Lean.Json :=
  Lean.Json.arr <| (p.termsList.map fun term =>
    Lean.Json.arr #[
      Lean.Json.arr (term.1.toList.map (fun exponent =>
        Lean.Json.num (Lean.JsonNumber.fromNat exponent))).toArray,
      Lean.Json.num (Lean.JsonNumber.fromInt term.2)]).toArray

private def jsonError (context : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => return value
  | .error msg => throw <| IO.userError s!"{context}: {msg}"

private def jsonToTerms (nvars : Nat) (value : Lean.Json) :
    IO (List (List Nat × Int)) := do
  let encoded ← jsonError "FLINT multivariate result is not an array"
    value.getArr?
  let mut out : Array (List Nat × Int) := Array.mkEmpty encoded.size
  for encodedTerm in encoded do
    let pair ← jsonError "FLINT multivariate term is not an array"
      encodedTerm.getArr?
    let (exponentsValue, coefficientValue) ←
      match pair.toList with
      | [exponents, coefficient] => pure (exponents, coefficient)
      | _ => throw (IO.userError
          "FLINT multivariate term must contain exponents and coefficient")
    let encodedExponents ← jsonError
      "FLINT multivariate exponents are not an array" exponentsValue.getArr?
    unless encodedExponents.size = nvars do
      throw (IO.userError
        s!"FLINT multivariate exponent arity {encodedExponents.size}; expected {nvars}")
    let mut exponents : Array Nat := Array.mkEmpty nvars
    for encodedExponent in encodedExponents do
      exponents := exponents.push (← jsonError
        "FLINT multivariate exponent is not a natural" encodedExponent.getNat?)
    let coefficient ← jsonError
      "FLINT multivariate coefficient is not an integer" coefficientValue.getInt?
    if coefficient = 0 then
      throw <| IO.userError "FLINT multivariate result contains a zero coefficient"
    out := out.push (exponents.toList, coefficient)
  return out.toList

initialize coprime1 : IO.Ref CoprimeInput ← IO.mkRef (prepCoprime 1)

def runLeanCoprime2 (_ : Unit) : IO (List (List Nat × Int)) := do
  let input ← coprime1.get
  return terms (gcd input.left input.right)

def runFlintCoprime2 (_ : Unit) : IO (List (List Nat × Int)) := do
  let input ← coprime1.get
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mpoly" "gcd" #[
    ("nvars", Lean.Json.num (Lean.JsonNumber.fromNat 2)),
    ("a", termsJson input.left), ("b", termsJson input.right)]
  jsonToTerms 2 result

/-- Persistent-driver framing/dispatch calibration without polynomial work. -/
def runFlintMpolyOverhead (_ : Unit) : IO (List (List Nat × Int)) := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mpoly" "overhead" #[]
  jsonToTerms 2 result

def leanCompareConfig (expectedHash : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 12.0, minTotalSeconds := 0.2,
    expectedHash := some expectedHash }

def flintCompareConfig (expectedHash : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 12.0, minTotalSeconds := 0.2,
    warmupFirstIter := true, expectedHash := some expectedHash }

end Hex.MvGcdBench.Flint
