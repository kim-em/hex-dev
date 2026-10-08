/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealClosure.TowerRoots
public import HexRealAlgebraic.Roots
public import Lean.Data.Json

public section

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

private initialize nativeInput : IO.Ref (Option (DensePoly base.Value)) ← IO.mkRef (some nativeHead)
initialize trivialInput : IO.Ref (Option RealAlgebraicPoly) ← IO.mkRef (some trivialHead)

private def emitStage (backend stage : String) (elapsed count : Nat) : IO Unit := do
  IO.println <| (Lean.Json.mkObj [
    ("workload", Lean.toJson "metitarski"), ("backend", Lean.toJson backend),
    ("stage", Lean.toJson stage), ("elapsed_ns", Lean.toJson elapsed),
    ("root_count", Lean.toJson count)]).compress
  (← IO.getStdout).flush

private def emitSetup (backend : String) (elapsed degree : Nat) : IO Unit := do
  IO.println <| (Lean.Json.mkObj [("workload", Lean.toJson "metitarski"),
    ("backend", Lean.toJson backend), ("stage", Lean.toJson "second-construction"),
    ("elapsed_ns", Lean.toJson elapsed), ("degree", Lean.toJson degree)]).compress
  (← IO.getStdout).flush

/-- Exact rational Sturm counting in the independent input oracle isolates
only the least root in this interval. -/
private def leastLower : Rat := -1875 / 2048
private def leastUpper : Rat := -1875 / 4096

private def emitSelection (backend : String) : IO Unit := do
  IO.println <| (Lean.Json.mkObj [("workload", Lean.toJson "metitarski"),
    ("backend", Lean.toJson backend), ("stage", Lean.toJson "first-selection"),
    ("lower", Lean.toJson [leastLower.num, (leastLower.den : Int)]),
    ("upper", Lean.toJson [leastUpper.num, (leastUpper.den : Int)]),
    ("checked", Lean.toJson true)]).compress
  (← IO.getStdout).flush

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
  unless roots.length == 3 &&
      first.root.signAt (DensePoly.ofCoeffs #[⟨-leastLower⟩, 1]) == 1 &&
      first.root.signAt (DensePoly.ofCoeffs #[⟨-leastUpper⟩, 1]) == -1 do
    throw (IO.userError "MetiTarski least root differs from independent interval")
  emitSelection "native"
  let owner := first.root.context
  let alpha := first.root.value
  let y : DensePoly owner.Value := DensePoly.ofCoeffs #[0, 1]
  let setupStart ← IO.monoNanosNow
  let second := y * y * y + DensePoly.C (alpha * alpha * alpha + 1)
  let ref ← IO.mkRef (some second)
  emitSetup "native" ((← IO.monoNanosNow) - setupStart) second.natDegree
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

private def json (value : SignDet.Codec.Json) : IO Lean.Json := do
  let some text := String.fromUTF8? value.writeBytes
    | throw (IO.userError "invalid encoded UTF-8")
  match Lean.Json.parse text with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

/-- Functional records for the declared odd-degree ladder over the same least
MetiTarski root. Root equations, multiplicities, and stored descriptor data
are emitted outside scientific timing. Only degree three is the paper input. -/
def scaling (degree : Nat) : IO Unit := do
  unless degree ∈ [3,5,7,9] do throw (IO.userError "unsupported scaling degree")
  let some input ← nativeInput.get | throw (IO.userError "missing scaling input")
  let .ok (.finite (first :: rest)) := base.roots? input
    | throw (IO.userError "missing first scaling root")
  unless rest.length == 2 && first.multiplicity == 1 &&
      first.root.signAt input == 0 &&
      first.root.signAt (DensePoly.ofCoeffs #[⟨-leastLower⟩, 1]) == 1 &&
      first.root.signAt (DensePoly.ofCoeffs #[⟨-leastUpper⟩, 1]) == -1 do
    throw (IO.userError "scaling predecessor selection failed")
  let .selected firstDescriptor _ _ := first.root
    | throw (IO.userError "scaling predecessor must be selected")
  let owner := first.root.context
  let alpha := first.root.value
  let y : owner.Poly := DensePoly.ofCoeffs #[0,1]
  let power := (List.range degree).foldl (fun p _ => p*y) (DensePoly.C 1)
  let head := power + DensePoly.C (alpha*alpha*alpha+1)
  let .ok (.finite [entry]) := owner.roots? head
    | throw (IO.userError "scaling complete roots failed")
  let .selected descriptor _ _ := entry.root
    | throw (IO.userError "scaling root must be selected")
  unless entry.multiplicity == 1 && entry.root.signAt head == 0 &&
      firstDescriptor.raw.check base.sign base.signature firstDescriptor.evidence &&
      descriptor.raw.check owner.sign owner.signature descriptor.evidence do
    throw (IO.userError "scaling root equation or replay failed")
  IO.println <| (Lean.Json.mkObj [
    ("schema", Lean.toJson (1 : Nat)), ("workload", Lean.toJson "metitarski-degree-ladder"),
    ("degree", Lean.toJson degree), ("first_coefficients", Lean.toJson (metiCoefficients.map
      fun q => [q.num,(q.den : Int)])),
    ("first", ← json (Tower.rootData base.codec firstDescriptor)),
    ("head", ← json (owner.writePoly head).value),
    ("root", ← json (Tower.rootData owner.codec descriptor)),
    ("root_count", Lean.toJson (1 : Nat)), ("multiplicity", Lean.toJson entry.multiplicity),
    ("equation_sign", Lean.toJson (entry.root.signAt head)),
    ("first_replay", Lean.toJson true), ("root_replay", Lean.toJson true)]).compress

/-- The same two inputs and least-root selection through the existing
canonical real-algebraic backend, with semantic checks after timing. -/
@[noinline] def canonical : IO Unit := do
  let some input ← trivialInput.get | throw (IO.userError "missing MetiTarski input")
  let start ← IO.monoNanosNow
  let .finite roots := input.roots
    | throw (IO.userError "MetiTarski first isolation returned all roots")
  let elapsed := (← IO.monoNanosNow) - start
  emitStage "canonical" "first-isolation" elapsed roots.size
  let some first := roots[0]? | throw (IO.userError "MetiTarski first isolation returned no roots")
  let alpha := first.root
  unless roots.size == 3 && (alpha - RealAlgebraicNumber.ofRat leastLower).sign == 1 &&
      (alpha - RealAlgebraicNumber.ofRat leastUpper).sign == -1 do
    throw (IO.userError "canonical least root differs from independent interval")
  emitSelection "canonical"
  let setupStart ← IO.monoNanosNow
  let second := RealAlgebraicPoly.ofArray #[alpha * alpha * alpha + 1, 0, 0, 1]
  let ref ← IO.mkRef (some second)
  emitSetup "canonical" ((← IO.monoNanosNow) - setupStart) 3
  let some secondInput ← ref.get | throw (IO.userError "missing second MetiTarski input")
  let start ← IO.monoNanosNow
  let .finite secondRoots := secondInput.roots
    | throw (IO.userError "MetiTarski second isolation returned all roots")
  let elapsed := (← IO.monoNanosNow) - start
  emitStage "canonical" "second-isolation" elapsed secondRoots.size
  let original := metiCoefficients.toList.map RealAlgebraicNumber.ofRat
  let secondCheck := [alpha * alpha * alpha + 1, 0, 0, 1]
  unless first.multiplicity == 1 && (DensePoly.evalCoeffList original alpha).sign == 0 &&
      secondRoots.size == 1 && secondRoots.all (fun entry =>
        entry.multiplicity == 1 && (DensePoly.evalCoeffList secondCheck entry.root).sign == 0) do
    throw (IO.userError "MetiTarski trivial root equation or multiplicity failed")
  IO.println <| (Lean.Json.mkObj [("workload", Lean.toJson "metitarski"),
    ("backend", Lean.toJson "canonical"), ("checked", Lean.toJson true)]).compress

end Hex.RealClosure.Phase4

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    for degree in [3,5,7,9] do Hex.RealClosure.Phase4.scaling degree
  | ["metitarski", "scaling", degree] =>
    let some n := degree.toNat? | throw (IO.userError "degree must be natural")
    Hex.RealClosure.Phase4.scaling n
  | ["metitarski", "native"] => Hex.RealClosure.Phase4.native
  | ["metitarski", "canonical"] | ["metitarski", "trivial"] => Hex.RealClosure.Phase4.canonical
  | _ => throw (IO.userError "usage: hexrealclosure_phase4 metitarski native|canonical|scaling DEGREE")
  return 0
