/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealClosure.Sample
import HexRealClosure.TowerEnlargement
import LeanBench
import Lean.Data.Json

namespace Hex.RealClosure.SampleMeasurements
open Hex.SignDet Tower

private def registry : BaseContext.Registry := fun _ => none
private def base : Context registry := Context.base (BaseContext.rational registry)

/-- Identical original boundaries and polynomials for all three methods. -/
structure Input where
  gap : Nat
  lower : Tower.Root base
  upper : Tower.Root base
  polynomials : List base.Poly

/-- Actual sample ownership and the original coefficient inclusion. -/
structure Result where
  context : Context registry
  value : context.Value
  embed : base.Value → context.Value
  cuts : Nat := 0

inductive Method where
  | midpoint | dyadic | infinitesimal
  deriving Repr

private def Method.label : Method → String
  | .midpoint => "midpoint"
  | .dyadic => "dyadic"
  | .infinitesimal => "infinitesimal"

private def prepare (gap : Nat) : Except String Input := do
  let x : base.Poly := DensePoly.ofCoeffs #[0, 1]
  let lower := x * x - DensePoly.C (1 + 1)
  let upper := lower - DensePoly.C (1 / NatCast.natCast (2 ^ gap))
  let select (head : base.Poly) : Except String (Tower.Root base) := do
    let some descriptor := Descriptor.validate base.sign base.signature
      { context := base.signature, head, lower := .finite 1, upper := .finite (1 + 1),
        indices := [], signs := [] } | throw "sample measurement boundary rejected"
    return Tower.Root.ofSelection base (.selected descriptor)
  return ⟨gap, ← select lower, ← select upper, [lower, upper]⟩

private def dyadic (input : Input) : Nat → base.Value → base.Value → Nat → Except String Result
  | 0, _, _, _ => .error "dyadic sample search exhausted its operational bound"
  | fuel + 1, lo, hi, cuts =>
    let middle := (lo + hi) / (1 + 1)
    let above := input.lower.compare (.point middle) == .lt
    let below := (Tower.Root.point middle).compare input.upper == .lt
    if above && below then .ok ⟨base, middle, id, cuts + 1⟩
    else if above then dyadic input fuel lo middle (cuts + 1)
    else dyadic input fuel middle hi (cuts + 1)

/-- Sample construction includes the actual shared-context collection or
infinitesimal rebuilding. Boundary production occurs before measurement. -/
def compute (input : Input) : Method → Except String Result
  | .midpoint =>
    let sample := (Sample.Region.between input.lower input.upper).sample
    .ok ⟨sample.input.context, sample.value, sample.input.value, 0⟩
  | .dyadic => dyadic input 512 1 (1 + 1) 0
  | .infinitesimal => do
    let some enlarged := input.lower.context.enlargeWithParameter?
      | throw "infinitesimal sample enlargement rejected"
    let value := enlarged.conversion.value input.lower.value + enlarged.parameter
    return ⟨enlarged.conversion.context, value,
      fun coefficient => enlarged.conversion.value (input.lower.embed coefficient), 0⟩

/-- Evaluate the same original polynomial family through the retained inclusion. -/
def Result.signs (result : Result) (input : Input) : List Int :=
  input.polynomials.map fun p => result.context.sign
    ((DensePoly.ofCoeffs (p.toArray.map result.embed)).eval result.value)

private def json (value : SignDet.Codec.Json) : IO Lean.Json :=
  match Lean.Json.parse (String.fromUTF8! value.writeBytes) with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

/-- IO stores executable consumers of the dependent input. The native owners
remain captured by each consumer, while its result is an ordinary IO value. -/
structure Prepared where
  gap : Nat
  run : Method → IO UInt64
  describe : Method → IO Lean.Json

private def prepared (input : Input) : Prepared where
  gap := input.gap
  run := fun method => do
    let .ok result := compute input method | throw (IO.userError "sample construction failed")
    unless result.context.sign result.value == 1 && result.signs input == [1, -1] do
      throw (IO.userError "sample is outside the original open sector")
    return 1
  describe := fun method => do
    let .ok result := compute input method | throw (IO.userError "sample construction failed")
    unless result.context.sign result.value == 1 && result.signs input == [1, -1] do throw (IO.userError "sample sign mismatch")
    return Lean.Json.mkObj [
      ("gap", Lean.toJson input.gap), ("method", Lean.toJson method.label),
      ("polynomials", ← json (.arr (input.polynomials.toArray.map (SignDet.Codec.poly base.codec)))),
      ("context", ← json result.context.signature.literal.toJson),
      ("value", ← json (result.context.codec.encode result.value)),
      ("signs", Lean.toJson (result.signs input)),
      ("value_sign", Lean.toJson (result.context.sign result.value)),
      ("dyadic_cuts", Lean.toJson result.cuts)]

initialize inputs : IO.Ref (Option (Array Prepared)) ← IO.mkRef none

def install : IO Unit := do
  let cases ← #[0, 4, 8, 12].mapM fun gap =>
    match prepare gap with
    | .ok input => pure (prepared input)
    | .error message => throw (IO.userError message)
  inputs.set (some cases)

private def getInput (gap : Nat) : IO Prepared := do
  let some cases ← inputs.get | throw (IO.userError "sample inputs are not installed")
  let some input := cases.find? (fun input => input.gap == gap)
    | throw (IO.userError "sample gap is not registered")
  return input

/-- The timed consumer forces sample construction and the two exact signs.
Serialization and functional reporting are separate from timing. -/
def measure (gap : Nat) (method : Method) (_ : Unit) : IO UInt64 := do
  (← getInput gap).run method

namespace Gap0

def midpoint := measure 0 .midpoint
def dyadic := measure 0 .dyadic
def infinitesimal := measure 0 .infinitesimal

setup_fixed_benchmark midpoint where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark dyadic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark infinitesimal where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Gap0

namespace Gap4

def midpoint := measure 4 .midpoint
def dyadic := measure 4 .dyadic
def infinitesimal := measure 4 .infinitesimal

setup_fixed_benchmark midpoint where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark dyadic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark infinitesimal where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Gap4

namespace Gap8

def midpoint := measure 8 .midpoint
def dyadic := measure 8 .dyadic
def infinitesimal := measure 8 .infinitesimal

setup_fixed_benchmark midpoint where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark dyadic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark infinitesimal where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Gap8

namespace Gap12

def midpoint := measure 12 .midpoint
def dyadic := measure 12 .dyadic
def infinitesimal := measure 12 .infinitesimal

setup_fixed_benchmark midpoint where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark dyadic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark infinitesimal where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Gap12

/-- Exact native inputs, outputs and sign vectors; records no timing. -/
def emit : IO Unit := do
  for gap in [0, 4, 8, 12] do
    let input ← getInput gap
    for method in [Method.midpoint, .dyadic, .infinitesimal] do
      IO.println (← input.describe method).compress

end Hex.RealClosure.SampleMeasurements

def main (args : List String) : IO UInt32 := do
  Hex.RealClosure.SampleMeasurements.install
  if args.isEmpty || args == ["emit"] then
    Hex.RealClosure.SampleMeasurements.emit
    return 0
  LeanBench.Cli.dispatch args
