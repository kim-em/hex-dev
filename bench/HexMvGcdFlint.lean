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

abbrev P (n : Nat) (R : Type) [Zero R] := MvPoly n R Mono.lex
abbrev P2 (R : Type) [Zero R] := P 2 R

abbrev IntTerms := List (List Nat × Int)
abbrev RatTerms := List (List Nat × Rat)

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

def intTerms {n : Nat} (p : P n Int) : IntTerms :=
  p.termsList.map fun term => (term.1.toList, term.2)

def intTermsJson {n : Nat} (p : P n Int) : Lean.Json :=
  Lean.Json.arr <| (p.termsList.map fun term =>
    Lean.Json.arr #[
      Lean.Json.arr (term.1.toList.map (fun exponent =>
        Lean.Json.num (Lean.JsonNumber.fromNat exponent))).toArray,
      Lean.Json.num (Lean.JsonNumber.fromInt term.2)]).toArray

def ratTerms {n : Nat} (p : P n Rat) : RatTerms :=
  p.termsList.map fun term => (term.1.toList, term.2)

def ratTermsJson {n : Nat} (p : P n Rat) : Lean.Json :=
  Lean.Json.arr <| (p.termsList.map fun term =>
    Lean.Json.arr #[
      Lean.Json.arr (term.1.toList.map (fun exponent =>
        Lean.Json.num (Lean.JsonNumber.fromNat exponent))).toArray,
      Lean.Json.arr #[
        Lean.Json.num (Lean.JsonNumber.fromInt term.2.num),
        Lean.Json.num (Lean.JsonNumber.fromNat term.2.den)]]).toArray

private def jsonError (context : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => return value
  | .error msg => throw <| IO.userError s!"{context}: {msg}"

def jsonToIntTerms (nvars : Nat) (value : Lean.Json) : IO IntTerms := do
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

def jsonToRatTerms (nvars : Nat) (value : Lean.Json) : IO RatTerms := do
  let encoded ← jsonError "FLINT multivariate result is not an array"
    value.getArr?
  let mut out : Array (List Nat × Rat) := Array.mkEmpty encoded.size
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
    let encodedCoefficient ← jsonError
      "FLINT multivariate rational coefficient is not an array"
      coefficientValue.getArr?
    let (numValue, denValue) ← match encodedCoefficient.toList with
      | [num, den] => pure (num, den)
      | _ => throw (IO.userError
          "FLINT multivariate rational coefficient must contain numerator and denominator")
    let num ← jsonError "FLINT rational numerator is not an integer" numValue.getInt?
    let den ← jsonError "FLINT rational denominator is not a natural" denValue.getNat?
    if hden : den = 0 then
      throw <| IO.userError "FLINT rational denominator is zero"
    else
      let coefficient := Rat.normalize num den hden
      if coefficient = 0 then
        throw <| IO.userError "FLINT multivariate result contains a zero coefficient"
      out := out.push (exponents.toList, coefficient)
  return out.toList

def leanIntGcd {n : Nat} (input : P n Int × P n Int) : IO IntTerms :=
  return intTerms (gcd input.1 input.2)

def intGcd {n : Nat} (input : P n Int × P n Int) : IO IntTerms := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mpoly" "gcd" #[
    ("nvars", Lean.Json.num (Lean.JsonNumber.fromNat n)),
    ("a", intTermsJson input.1), ("b", intTermsJson input.2)]
  jsonToIntTerms n result

def intDiv {n : Nat} (dividend divisor : P n Int) : IO IntTerms := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mpoly" "divexact" #[
    ("nvars", Lean.Json.num (Lean.JsonNumber.fromNat n)),
    ("a", intTermsJson dividend), ("b", intTermsJson divisor)]
  jsonToIntTerms n result

def intSquarefree {n : Nat} (polynomial : P n Int) : IO (List Nat) := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mpoly" "squarefree" #[
    ("nvars", Lean.Json.num (Lean.JsonNumber.fromNat n)),
    ("a", intTermsJson polynomial)]
  let values ← jsonError "FLINT squarefree result is not an array" result.getArr?
  values.toList.mapM fun value =>
    jsonError "FLINT squarefree multiplicity is not a natural" value.getNat?

def leanRatGcd {n : Nat} (input : P n Rat × P n Rat) : IO RatTerms :=
  return ratTerms (gcd input.1 input.2)

def ratGcd {n : Nat} (input : P n Rat × P n Rat) : IO RatTerms := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpq_mpoly" "gcd" #[
    ("nvars", Lean.Json.num (Lean.JsonNumber.fromNat n)),
    ("a", ratTermsJson input.1), ("b", ratTermsJson input.2)]
  jsonToRatTerms n result

initialize coprime1 : IO.Ref CoprimeInput ← IO.mkRef (prepCoprime 1)

def runLeanCoprime2 (_ : Unit) : IO IntTerms := do
  let input ← coprime1.get
  leanIntGcd (input.left, input.right)

def runFlintCoprime2 (_ : Unit) : IO IntTerms := do
  let input ← coprime1.get
  intGcd (input.left, input.right)

/-- Persistent-driver framing/dispatch calibration without polynomial work. -/
def runFlintMpolyOverhead (_ : Unit) : IO IntTerms := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mpoly" "overhead" #[]
  jsonToIntTerms 2 result

def leanCompareConfig (expectedHash : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 12.0, minTotalSeconds := 0.2,
    expectedHash := some expectedHash }

def flintCompareConfig (expectedHash : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 12.0, minTotalSeconds := 0.2,
    warmupFirstIter := true, expectedHash := some expectedHash }

end Hex.MvGcdBench.Flint
