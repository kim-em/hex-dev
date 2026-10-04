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

instance : Hashable Input where
  hash input := hash (input.context.root.raw.head.toArray, input.working.toArray, input.steps)

/-- Prepare the positive root of `2X^degree - 1` in `(0,1)`. Neither storage
arm changes this descriptor, its selected embedding or its sign backend. -/
def prepare (degree : Nat) : Option Input := do
  let head : DensePoly Rat := DensePoly.monomial degree 2 - DensePoly.C 1
  let raw : SignDet.RawDescriptor Rat Unit :=
    { context := (), head, lower := .finite 0, upper := .finite 1,
      indices := [], signs := [] }
  let descriptor ← SignDet.Descriptor.validate OrderedFn.orderSign () raw
  let context := Algebraic.Context.adjoin descriptor (fun q => decide (q.den = 1))
  return ⟨context, DensePoly.monicize head, 2 * degree⟩

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
    Algebraic.Element.ofPoly (DensePoly.divMod (a.polynomial * seed.polynomial) input.working).2) 1

/-- The result is a positive value; missing input or a failed result returns a
nonmatching hash which measurement runners must reject. -/
def runClean (input : Option Input) : UInt64 :=
  match input with
  | none => 0
  | some input => if (clean input).sign == 1 then 1 else 0

/- Cost model: cubic degree scaling is a hypothesis. With 2n multiplies,
retained degrees are O(n); dense multiplication and polynomial reduction
cost O(n^2) coefficient operations per step. Coefficient bit growth and
selected-root sign work are measured separately and can exceed this model. -/
setup_benchmark runClean n => n ^ 3
  with prep := prepare
  where {
    paramFloor := 2, paramCeiling := 16
    paramSchedule := .custom #[2, 4, 8, 16]
    maxSecondsPerCall := 120.0
    targetInnerNanos := 500000000
    signalFloorMultiplier := 1.0
  }

/-- Eager arm of the same arithmetic trace. -/
def runEager (input : Option Input) : UInt64 :=
  match input with
  | none => 0
  | some input => if (eager input).sign == 1 then 1 else 0

/- Cost model: the eager arm has 2n products and reductions on degree-O(n)
dense representatives, giving a cubic coefficient-operation hypothesis.
Rational denominator growth and selected-root queries remain unbounded by
this degree-only model and must be reported with the actual measurements. -/
setup_benchmark runEager n => n ^ 3
  with prep := prepare
  where {
    paramFloor := 2, paramCeiling := 16
    paramSchedule := .custom #[2, 4, 8, 16]
    maxSecondsPerCall := 120.0
    targetInnerNanos := 500000000
    signalFloorMultiplier := 1.0
  }

private def coefficients (p : DensePoly Rat) : Lean.Json :=
  Lean.toJson (p.toArray.map fun q => [q.num, (q.den : Int)])

private def storage {context : Context} (a : Algebraic.Element context) : Lean.Json :=
  Lean.Json.mkObj [("coefficients", coefficients a.polynomial),
    ("degree", Lean.toJson a.polynomial.natDegree), ("clean", Lean.toJson a.isClean),
    ("sign", Lean.toJson a.sign)]

/-- Untimed semantic and representation checks accompany each measured size.
The independent exact oracle also checks the retained polynomials modulo the
literal defining head, rather than accepting the matching positive hashes. -/
def emit (degree : Nat) : IO Unit := do
  let some input := prepare degree | throw (IO.userError "normalization input rejected")
  let a := clean input
  let b := eager input
  unless (a - b).sign == 0 && a.sign == 1 && b.sign == 1 do
    throw (IO.userError "normalization arms disagree at the selected root")
  IO.println <| (Lean.Json.mkObj [("degree", Lean.toJson degree),
    ("steps", Lean.toJson input.steps), ("head", coefficients input.context.root.raw.head),
    ("working_head", coefficients input.working), ("clean", storage a),
    ("eager", storage b), ("equal_at_root", Lean.toJson true)]).compress

end Hex.RealClosure.Normalization

def main (args : List String) : IO UInt32 := do
  match args with
  | ["storage", degree] =>
    let some n := degree.toNat? | throw (IO.userError "degree must be a natural number")
    Hex.RealClosure.Normalization.emit n
    return 0
  | _ => LeanBench.Cli.dispatch args
