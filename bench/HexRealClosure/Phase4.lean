/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealClosure.TowerRoots
import HexRealClosure.TrivialTower
import Lean.Data.Json

namespace Hex.RealClosure.Phase4

/-- Ascending coefficients of the degree-15 MetiTarski trace in de Moura
and Passmore, CADE 2013, section 4. The second input is `Y³ + x³ + 1`,
where `x` is the least real root of this exact polynomial. -/
def metiCoefficients : Array Rat := #[592704, 402192, 90972, 3266731,
  -931392, -193914, -5792221, 756756, 140742, 3046158, -259308,
  -42336, -520884, 31752, 4536, 216]

private def registry : BaseContext.Registry := fun _ => none
private def base := Tower.Context.base (BaseContext.rational registry)
private def nativeHead : DensePoly base.Value :=
  DensePoly.ofCoeffs (metiCoefficients.map fun q => ⟨q⟩)
private def trivialHead : RealAlgebraicPoly :=
  RealAlgebraicPoly.ofArray (metiCoefficients.map RealAlgebraicNumber.ofRat)

initialize nativeInput : IO.Ref (Option (DensePoly base.Value)) ← IO.mkRef (some nativeHead)
initialize trivialInput : IO.Ref (Option RealAlgebraicPoly) ← IO.mkRef (some trivialHead)

private def emitStage (backend stage : String) (elapsed count : Nat) : IO Unit :=
  IO.println <| (Lean.Json.mkObj [
    ("workload", Lean.toJson "metitarski"), ("backend", Lean.toJson backend),
    ("stage", Lean.toJson stage), ("elapsed_ns", Lean.toJson elapsed),
    ("root_count", Lean.toJson count)]).compress

/-- Run the actual native complete-root API at both successive levels.
Semantic zero and multiplicity checks are outside the isolation timings. -/
@[noinline] def native : IO Unit := do
  let some input ← nativeInput.get | throw (IO.userError "missing MetiTarski input")
  let start ← IO.monoNanosNow
  let .ok (.finite roots) := base.roots? input
    | throw (IO.userError "MetiTarski first isolation failed")
  let elapsed := (← IO.monoNanosNow) - start
  emitStage "native" "first-isolation" elapsed roots.length
  let first :: _ := roots | throw (IO.userError "MetiTarski first isolation returned no roots")
  let owner := first.root.context
  let alpha := first.root.value
  let y : DensePoly owner.Value := DensePoly.ofCoeffs #[0, 1]
  let second := y * y * y + DensePoly.C (alpha * alpha * alpha + 1)
  let ref ← IO.mkRef (some second)
  let some secondInput ← ref.get | throw (IO.userError "missing second MetiTarski input")
  let start ← IO.monoNanosNow
  let .ok (.finite secondRoots) := owner.roots? secondInput
    | throw (IO.userError "MetiTarski second isolation failed")
  let elapsed := (← IO.monoNanosNow) - start
  emitStage "native" "second-isolation" elapsed secondRoots.length
  unless first.multiplicity == 1 && first.root.signAt input == 0 &&
      secondRoots.length == 1 && secondRoots.all (fun entry =>
        entry.multiplicity == 1 && entry.root.signAt secondInput == 0) do
    throw (IO.userError "MetiTarski native root equation or multiplicity failed")
  IO.println <| (Lean.Json.mkObj [("workload", Lean.toJson "metitarski"),
    ("backend", Lean.toJson "native"), ("checked", Lean.toJson true),
    ("first_context_depth", Lean.toJson owner.signature.roots.length)]).compress

/-- The same two inputs and least-root selection through the existing
canonical real-algebraic backend, with semantic checks after timing. -/
@[noinline] def trivial : IO Unit := do
  let some input ← trivialInput.get | throw (IO.userError "missing MetiTarski input")
  let start ← IO.monoNanosNow
  let .finite roots := input.roots
    | throw (IO.userError "MetiTarski first isolation returned all roots")
  let elapsed := (← IO.monoNanosNow) - start
  emitStage "trivial" "first-isolation" elapsed roots.size
  let some first := roots[0]? | throw (IO.userError "MetiTarski first isolation returned no roots")
  let alpha := first.root
  let second := RealAlgebraicPoly.ofArray #[alpha * alpha * alpha + 1, 0, 0, 1]
  let ref ← IO.mkRef (some second)
  let some secondInput ← ref.get | throw (IO.userError "missing second MetiTarski input")
  let start ← IO.monoNanosNow
  let .finite secondRoots := secondInput.roots
    | throw (IO.userError "MetiTarski second isolation returned all roots")
  let elapsed := (← IO.monoNanosNow) - start
  emitStage "trivial" "second-isolation" elapsed secondRoots.size
  let original := metiCoefficients.toList.map RealAlgebraicNumber.ofRat
  let secondCheck := [alpha * alpha * alpha + 1, 0, 0, 1]
  unless first.multiplicity == 1 && (DensePoly.evalCoeffList original alpha).sign == 0 &&
      secondRoots.size == 1 && secondRoots.all (fun entry =>
        entry.multiplicity == 1 && (DensePoly.evalCoeffList secondCheck entry.root).sign == 0) do
    throw (IO.userError "MetiTarski trivial root equation or multiplicity failed")
  IO.println <| (Lean.Json.mkObj [("workload", Lean.toJson "metitarski"),
    ("backend", Lean.toJson "trivial"), ("checked", Lean.toJson true)]).compress

end Hex.RealClosure.Phase4

def main (args : List String) : IO UInt32 := do
  match args with
  | ["metitarski", "native"] => Hex.RealClosure.Phase4.native
  | ["metitarski", "trivial"] => Hex.RealClosure.Phase4.trivial
  | _ => throw (IO.userError "usage: hexrealclosure_phase4 metitarski native|trivial")
  return 0
