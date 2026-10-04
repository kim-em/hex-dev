/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealClosure.Algebraic
import HexOrderedFn.Infinitesimal
import LeanBench
import Lean.Data.Json

namespace Hex.RealClosure.Normalization

private abbrev Context := Algebraic.Context Rat Unit OrderedFn.orderSign ()

/-- Both storage arms use this one checked root and coefficient backend. The
monic working polynomial is used only by the eager measurement arm. -/
structure Input where
  context : Context
  working : DensePoly Rat
  steps : Nat
  monic : working.leadingCoeff = 1

/-- Prepare the positive root of `2X^degree - 1` in `(0,1)`. Neither storage
arm changes this descriptor, its selected embedding or its sign backend. -/
def prepare (degree : Nat) : Option Input := do
  let head : DensePoly Rat := DensePoly.monomial degree 2 - DensePoly.C 1
  let raw : SignDet.RawDescriptor Rat Unit :=
    { context := (), head, lower := .finite 0, upper := .finite 1,
      indices := [], signs := [] }
  let descriptor ← SignDet.Descriptor.validate OrderedFn.orderSign () raw
  let context := Algebraic.Context.adjoin descriptor (fun q => decide (q.den = 1))
  let working := DensePoly.monicize head
  if monic : working.leadingCoeff = 1 then
    return ⟨context, working, 2 * degree, monic⟩
  else none

/-- Retain the library's actual clean packing after each multiplication. -/
def clean (input : Input) : Algebraic.Element input.context :=
  let seed : Algebraic.Element input.context := Algebraic.Element.ofPoly (DensePoly.ofCoeffs #[1, 1])
  (List.range input.steps).foldl (fun a _ => a * seed) 1

/-- Eagerly reduce each identical product modulo the monic working definition,
then use the same library zero/sign packing in the original immutable owner.
This is a measurement baseline; it changes no production storage policy. -/
def eager (input : Input) : Algebraic.Element input.context :=
  let seed : Algebraic.Element input.context := Algebraic.Element.ofPoly (DensePoly.ofCoeffs #[1, 1])
  (List.range input.steps).foldl (fun a _ =>
    Algebraic.Element.ofPoly (DensePoly.divModMonic (a.polynomial * seed.polynomial) input.working input.monic).2) 1

/-- Fingerprint all stored coefficients and the cached sign. Exact arithmetic
is checked independently; the oracle checks these fixed endpoints stay below integer truncation. -/
def resultHash {context : Context} (a : Algebraic.Element context) : UInt64 :=
  hash (a.polynomial.toArray.map (fun q => (q.num, q.den)), a.sign)

def runClean (input : Option Input) : UInt64 :=
  match input with
  | none => 0
  | some input => let a := clean input; if a.sign == 1 then resultHash a else 0

def runEager (input : Option Input) : UInt64 :=
  match input with
  | none => 0
  | some input => let a := eager input; if a.sign == 1 then resultHash a else 0

/- Fixed comparison endpoints: these registrations bind exact result hashes
for the four matched inputs. They make no asymptotic claim and do not discharge
Phase-4 scaling coverage. Linear-seed multiplication and eager monic division
are linear per step. The unique selected root uses direct Sturm queries rather
than BKR; degree 2 uses the linear endpoint fast path instead. Clean
queries also pseudo-divide the retained higher-degree polynomial. Rational bit
growth prevents deriving a tight wall-time model from the cubic field-operation
estimate alone. A general timeout is an operational cap, not a regression budget.
Preparation is installed in the reference before the harness starts timing. -/
initialize measurementInputs : IO.Ref (List (Nat × Input)) ← IO.mkRef []

def clean2 (_ : Unit) : IO UInt64 := do
  return runClean (((← measurementInputs.get).find? (fun input => input.1 == 2)).map Prod.snd)

setup_fixed_benchmark clean2 where {
  expectedHash := some 0x3412eccad34759ea
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def clean4 (_ : Unit) : IO UInt64 := do
  return runClean (((← measurementInputs.get).find? (fun input => input.1 == 4)).map Prod.snd)

setup_fixed_benchmark clean4 where {
  expectedHash := some 0x94e8f7be8d8094d5
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def clean8 (_ : Unit) : IO UInt64 := do
  return runClean (((← measurementInputs.get).find? (fun input => input.1 == 8)).map Prod.snd)

setup_fixed_benchmark clean8 where {
  expectedHash := some 0x7fafce5255084bbd
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def clean16 (_ : Unit) : IO UInt64 := do
  return runClean (((← measurementInputs.get).find? (fun input => input.1 == 16)).map Prod.snd)

setup_fixed_benchmark clean16 where {
  expectedHash := some 0x992873940e7a7ca3
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def eager2 (_ : Unit) : IO UInt64 := do
  return runEager (((← measurementInputs.get).find? (fun input => input.1 == 2)).map Prod.snd)

setup_fixed_benchmark eager2 where {
  expectedHash := some 0xe368522d9dc1d2f2
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def eager4 (_ : Unit) : IO UInt64 := do
  return runEager (((← measurementInputs.get).find? (fun input => input.1 == 4)).map Prod.snd)

setup_fixed_benchmark eager4 where {
  expectedHash := some 0x319b3437a6d96431
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def eager8 (_ : Unit) : IO UInt64 := do
  return runEager (((← measurementInputs.get).find? (fun input => input.1 == 8)).map Prod.snd)

setup_fixed_benchmark eager8 where {
  expectedHash := some 0xcfa38add5d03e099
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def eager16 (_ : Unit) : IO UInt64 := do
  return runEager (((← measurementInputs.get).find? (fun input => input.1 == 16)).map Prod.snd)

setup_fixed_benchmark eager16 where {
  expectedHash := some 0x72603d1a602928b2
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

private def coefficients (p : DensePoly Rat) : Lean.Json :=
  Lean.toJson (p.toArray.map fun q => [q.num, (q.den : Int)])

private def storage {context : Context} (a : Algebraic.Element context) : Lean.Json :=
  Lean.Json.mkObj [("coefficients", coefficients a.polynomial),
    ("query_coefficients", coefficients (context.queryPoly a.polynomial)),
    ("degree", Lean.toJson a.polynomial.natDegree), ("clean", Lean.toJson a.isClean),
    ("sign", Lean.toJson a.sign), ("result_hash", Lean.toJson (resultHash a).toNat)]

/-- Untimed semantic and representation checks accompany each measured size.
The independent exact oracle also checks the retained polynomials modulo the
literal defining head, rather than accepting the matching positive hashes. -/
def emit (degree : Nat) : IO Unit := do
  let some input := prepare degree | throw (IO.userError "normalization input rejected")
  let a := clean input
  let b := eager input
  unless (a - b).sign == 0 && a.sign == 1 && b.sign == 1 do
    throw (IO.userError "normalization arms disagree at the selected root")
  let prefixes := (List.range (input.steps + 1)).map fun step =>
    let partialInput := { input with steps := step }
    Lean.Json.mkObj [("step", Lean.toJson step), ("clean", storage (clean partialInput)),
      ("eager", storage (eager partialInput))]
  IO.println <| (Lean.Json.mkObj [("degree", Lean.toJson degree),
    ("steps", Lean.toJson input.steps), ("head", coefficients input.context.root.raw.head),
    ("working_head", coefficients input.working), ("clean", storage a),
    ("eager", storage b), ("equal_at_root", Lean.toJson true), ("prefixes", Lean.toJson prefixes)]).compress

end Hex.RealClosure.Normalization

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    for degree in [2, 4, 8, 16] do
      Hex.RealClosure.Normalization.emit degree
    return 0
  | ["storage", degree] =>
    let some n := degree.toNat? | throw (IO.userError "degree must be a natural number")
    Hex.RealClosure.Normalization.emit n
    return 0
  | _ =>
    let mut inputs := []
    for degree in [2, 4, 8, 16] do
      let some input := Hex.RealClosure.Normalization.prepare degree |
        throw (IO.userError "normalization input rejected")
      inputs := inputs ++ [(degree, input)]
    Hex.RealClosure.Normalization.measurementInputs.set inputs
    LeanBench.Cli.dispatch args
