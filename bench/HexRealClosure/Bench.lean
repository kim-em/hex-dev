/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealClosure.Element
import HexRealClosure.AlgebraicContext
import HexRealClosure.CompleteRoots
import HexRealClosure.TowerRoots
import LeanBench

namespace Hex.RealClosure.Bench

private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
private def head : DensePoly Rat :=
  (DensePoly.ofCoeffs #[-2, 0, 1]) * (x - DensePoly.C 3)

private def raw : SignDet.RawDescriptor Rat Nat :=
  { context := 7, head, lower := .finite 0, upper := .finite 4,
    indices := [1], signs := [-1] }

initialize rawRef : IO.Ref (Option (SignDet.RawDescriptor Rat Nat)) ← IO.mkRef (some raw)

/-- Functional timing anchor using the test polynomial `(X² - 2)(X - 3)`.
The interval `(0, 4)` contains two positive roots, and the derivative sign
selects `√2`. The call checks the selected value. The ten-second per-call cap
is an operational safeguard, not a performance claim. -/
def runCanonical : Unit → IO UInt64 := fun _ => do
  let some input ← rawRef.get
    | throw (IO.userError "canonical benchmark: missing input")
  let some d := Root.validate 7 input
    | throw (IO.userError "canonical benchmark: descriptor rejected")
  let a := d.toCanonical
  if a.sign == 1 && (a * a == Hex.RealAlgebraicNumber.ofRat 2) then
    return 1
  else
    throw (IO.userError "canonical benchmark: wrong selected root")

setup_fixed_benchmark runCanonical where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

/-- Functional timing anchor for packed arithmetic at the same selected root.
It includes nonliteral-zero packing, addition cancellation and gcd inversion.
The ten-second per-call cap is an operational safeguard. -/
def runPacked : Unit → IO UInt64 := fun _ => do
  let some input ← rawRef.get
    | throw (IO.userError "packed benchmark: missing input")
  let some d := Root.validate 7 input
    | throw (IO.userError "packed benchmark: descriptor rejected")
  let alpha : Element d := Element.ofPoly x
  let selectedZero : Element d := Element.ofPoly (x * x - DensePoly.C 2)
  let below : Element d := Element.ofPoly (x - DensePoly.C 3)
  if selectedZero == 0 && alpha + -alpha == 0 &&
      (below * below⁻¹).value == Hex.RealAlgebraicNumber.ofRat 1 then
    return 1
  else
    throw (IO.userError "packed benchmark: arithmetic mismatch")

setup_fixed_benchmark runPacked where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

/-- The same packed arithmetic with one canonical root cached per descriptor. -/
def runPackedCached : Unit → IO UInt64 := fun _ => do
  let some input ← rawRef.get
    | throw (IO.userError "cached packed benchmark: missing input")
  let some d := Root.validate 7 input
    | throw (IO.userError "cached packed benchmark: descriptor rejected")
  let h := d.handle
  let alpha := h.pack x
  let selectedZero := h.pack (x * x - DensePoly.C 2)
  let below := h.pack (x - DensePoly.C 3)
  if selectedZero == 0 && h.add alpha (h.neg alpha) == 0 &&
      h.value (h.mul below (h.inv below)) ==
        Hex.RealAlgebraicNumber.ofRat 1 then
    return 1
  else
    throw (IO.userError "cached packed benchmark: arithmetic mismatch")

setup_fixed_benchmark runPackedCached where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

/-- Functional timing anchor for polynomial division over packed coefficients.
The input is `Y² - 2` divided by `Y - √2`, with the selected root
from the test polynomial. The ten-second cap is an operational safeguard. -/
def runPoly : Unit → IO UInt64 := fun _ => do
  let some input ← rawRef.get
    | throw (IO.userError "polynomial benchmark: missing input")
  let some d := Root.validate 7 input
    | throw (IO.userError "polynomial benchmark: descriptor rejected")
  let alpha : Element d := Element.ofPoly x
  let y : DensePoly (Element d) := DensePoly.ofCoeffs #[0, 1]
  let divisor := y - DensePoly.C alpha
  let dividend := y * y - DensePoly.C 2
  let (quotient, remainder) := DensePoly.divMod dividend divisor
  if remainder.isZero && quotient.natDegree == 1 &&
      (quotient.eval (0 : Element d)).value == alpha.value then
    return 1
  else
    throw (IO.userError "polynomial benchmark: wrong quotient or remainder")

setup_fixed_benchmark runPoly where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

/-- The same polynomial division with coefficients sharing one root handle. -/
def runPolyCached : Unit → IO UInt64 := fun _ => do
  let some input ← rawRef.get
    | throw (IO.userError "cached polynomial benchmark: missing input")
  let some d := Root.validate 7 input
    | throw (IO.userError "cached polynomial benchmark: descriptor rejected")
  let h := d.handle
  let alpha : Root.Handle.Value h := Root.Handle.Value.ofPoly h x
  let y : DensePoly (Root.Handle.Value h) := DensePoly.ofCoeffs #[0, 1]
  let divisor := y - DensePoly.C alpha
  let dividend := y * y - DensePoly.C 2
  let (quotient, remainder) := DensePoly.divMod dividend divisor
  if remainder.isZero && quotient.natDegree == 1 &&
      (quotient.eval (0 : Root.Handle.Value h)).value == alpha.value then
    return 1
  else
    throw (IO.userError "cached polynomial benchmark: wrong quotient or remainder")

setup_fixed_benchmark runPolyCached where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

/-- Functional timing anchor for the full descriptor validation, cofactor
split, context rebind and polynomial transport path, including selected-root
enumeration inside coefficient packing. -/
def runTransport : Unit → IO UInt64 := fun _ => do
  let some input ← rawRef.get
    | throw (IO.userError "transport benchmark: missing input")
  let some d := Root.validate 7 input
    | throw (IO.userError "transport benchmark: descriptor rejected")
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let some (some r) := (below.split? 8 (.finite 1) (.finite 2)).toOption
    | throw (IO.userError "transport benchmark: split rejected")
  let alpha : Element d := Element.ofPoly x
  let zero : Element d := Element.ofPoly (x * x - DensePoly.C 2)
  let square : Element d := Element.ofPoly (x * x)
  let p : DensePoly (Element d) := DensePoly.ofCoeffs #[alpha, zero, square, alpha]
  let encoded := Element.transportPoly r.encoding p
  let rebound := Element.rebindPoly r.binding encoded
  let refined := Element.refinePoly r p
  if encoded.natDegree == 3 && rebound.natDegree == 3 &&
      refined.natDegree == 3 && (refined.coeff 1) == 0 &&
      (p.coeff 2).polynomial.natDegree == 2 &&
      (refined.coeff 2).polynomial.natDegree == 0 then
    return 1
  else
    throw (IO.userError "transport benchmark: unexpected polynomial shape")

setup_fixed_benchmark runTransport where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

/-- The same full split-and-transport path, with one cached root per context. -/
def runTransportCached : Unit → IO UInt64 := fun _ => do
  let some input ← rawRef.get
    | throw (IO.userError "cached transport benchmark: missing input")
  let some d := Root.validate 7 input
    | throw (IO.userError "cached transport benchmark: descriptor rejected")
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let some (some r) := (below.split? 8 (.finite 1) (.finite 2)).toOption
    | throw (IO.userError "cached transport benchmark: split rejected")
  let source := d.handle
  let encodedHandle := Root.handle r.encoding.target
  let target := Root.handle r.binding.target
  let alpha := source.pack x
  let zero := source.pack (x * x - DensePoly.C 2)
  let square := source.pack (x * x)
  let p : DensePoly (Element d) := DensePoly.ofCoeffs #[alpha, zero, square, alpha]
  let encoded := Element.transportPolyWith r.encoding encodedHandle p
  let rebound := Element.rebindPolyWith r.binding target encoded
  let refined := Element.refinePolyWith r target p
  if encoded.natDegree == 3 && rebound.natDegree == 3 &&
      refined.natDegree == 3 && (refined.coeff 1) == 0 &&
      (p.coeff 2).polynomial.natDegree == 2 &&
      (refined.coeff 2).polynomial.natDegree == 0 then
    return 1
  else
    throw (IO.userError "cached transport benchmark: unexpected polynomial shape")

setup_fixed_benchmark runTransportCached where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

/-- Functional timing anchor for general selected-root arithmetic. The input
and semantic checks match the rational packed anchor. This includes descriptor
validation, nonliteral-zero packing, cancellation and local gcd inversion;
it makes no complexity claim. -/
def runGeneral : Unit → IO UInt64 := fun _ => do
  let some input ← rawRef.get
    | throw (IO.userError "general arithmetic benchmark: missing input")
  let some d := SignDet.Descriptor.validate Sturm.orderSign 7 input
    | throw (IO.userError "general arithmetic benchmark: descriptor rejected")
  let context := Algebraic.Context.adjoin d (fun q => q.den == 1)
  let alpha := Algebraic.Element.ofPoly (context := context) x
  let selectedZero := Algebraic.Element.ofPoly (context := context) (x * x - DensePoly.C 2)
  let below := Algebraic.Element.ofPoly (context := context) (x - DensePoly.C 3)
  if selectedZero == 0 && alpha + -alpha == 0 &&
      (below * below⁻¹ - 1).sign == 0 then
    return 1
  else
    throw (IO.userError "general arithmetic benchmark: arithmetic mismatch")

setup_fixed_benchmark runGeneral where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

private def repeated : DensePoly Rat :=
  DensePoly.scale (-3) (x * x * (x * x - 2) * (x * x - 2) * (x * x - 2) *
    (x - 3) * (x - 3) * (x - 3) * (x - 3) * (x - 3))

initialize repeatedRef : IO.Ref (Option (DensePoly Rat)) ← IO.mkRef (some repeated)
initialize isolationRef : IO.Ref (Option (DensePoly Rat)) ← IO.mkRef (some head)

/-- Timed Yun recurrence on the nonzero quotient after exact zero extraction.
The matching assembly anchor below includes both stages and factor isolation. -/
def runYun : Unit → IO UInt64 := fun _ => do
  let some p ← repeatedRef.get
    | throw (IO.userError "Yun benchmark: missing input")
  let (quotient, multiplicity) := ZeroFactor.remove p
  match Yun.decomposeRaw quotient with
  | .zero => throw (IO.userError "Yun benchmark: nonzero quotient rejected")
  | .factors _ factors =>
    if multiplicity == 2 && factors.size == 2 &&
        factors.any (fun factor => factor.2 == 3) &&
        factors.any (fun factor => factor.2 == 5) then
      return 1
    else
      throw (IO.userError "Yun benchmark: incorrect multiplicity factors")

setup_fixed_benchmark runYun where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

/-- Timed capped isolation plus descriptor completion for three real roots.
This includes production of the shared root certificates. -/
def runIsolation : Unit → IO UInt64 := fun _ => do
  let some input ← isolationRef.get
    | throw (IO.userError "isolation benchmark: missing input")
  match Isolation.complete? Sturm.orderSign (10378 : Nat) input with
  | .ok (some completion) =>
    if completion.roots.points.length + completion.roots.descriptors.length == 3 then
      return 1
    else
      throw (IO.userError "isolation benchmark: incorrect root count")
  | _ => throw (IO.userError "isolation benchmark: producer failed")

setup_fixed_benchmark runIsolation where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

/-- Timed zero extraction, Yun recurrence and isolation of every actual
factor. The repeated rational input has four distinct real roots with labels
2, 3, 3 and 5. -/
def runAssembly : Unit → IO UInt64 := fun _ => do
  let some p ← repeatedRef.get
    | throw (IO.userError "assembly benchmark: missing input")
  match Roots.assemble Sturm.orderSign (10378 : Nat) p with
  | .ok (.finite entries) =>
    if entries.length == 4 &&
        (entries.filter (fun e => e.multiplicity == 2)).length == 1 &&
        (entries.filter (fun e => e.multiplicity == 3)).length == 2 &&
        (entries.filter (fun e => e.multiplicity == 5)).length == 1 then
      return 1
    else
      throw (IO.userError "assembly benchmark: incorrect root labels")
  | _ => throw (IO.userError "assembly benchmark: producer failed")

setup_fixed_benchmark runAssembly where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

/-- Functional timing anchor for the complete root operation, including its
global comparisons and sorting. This anchor makes no asymptotic claim; Phase-4
scaling evidence is supplied separately. Labels are checked in root order. -/
def runRoots : Unit → IO UInt64 := fun _ => do
  let some p ← repeatedRef.get
    | throw (IO.userError "complete roots benchmark: missing input")
  match Roots.roots Sturm.orderSign (10378 : Nat) p with
  | .finite entries =>
    if entries.map (·.multiplicity) == [3, 2, 3, 5] then
      return 1
    else
      throw (IO.userError "complete roots benchmark: incorrect ordered labels")
  | .all => throw (IO.userError "complete roots benchmark: unexpected all-roots result")

setup_fixed_benchmark runRoots where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

private def nativeRegistry : BaseContext.Registry := fun _ => none
private def nativeBase := Tower.Context.base (BaseContext.rational nativeRegistry)

private def nativeRepeated : DensePoly nativeBase.Value :=
  let two : nativeBase.Value := 1 + 1
  let three : nativeBase.Value := two + 1
  let x : DensePoly nativeBase.Value := DensePoly.ofCoeffs #[0, 1]
  let quadratic := x * x - DensePoly.C two
  let linear := x - DensePoly.C three
  DensePoly.scale (-three) (x * x * quadratic * quadratic * quadratic *
    linear * linear * linear * linear * linear)

initialize nativeRepeatedRef : IO.Ref (Option (DensePoly nativeBase.Value)) ←
  IO.mkRef (some nativeRepeated)

/-- The same repeated-factor input as `runRoots`, including eager construction
of every selected native child, its descriptor encoding and prepared domain.
Input construction is outside the timed region. This is a functional anchor. -/
def runNativeRoots : Unit → IO UInt64 := fun _ => do
  let some p ← nativeRepeatedRef.get
    | throw (IO.userError "native roots benchmark: missing input")
  match nativeBase.roots? p with
  | .ok (.finite entries) =>
    if entries.map (·.multiplicity) == [3, 2, 3, 5] &&
        entries.all (fun entry =>
          entry.root.context.signature.base = nativeBase.signature.base &&
            entry.root.context.signature.roots.length ≤ 1) then
      return 1
    else
      throw (IO.userError "native roots benchmark: incorrect labels or child context")
  | _ => throw (IO.userError "native roots benchmark: producer failed")

setup_fixed_benchmark runNativeRoots where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

/-- Functional timing anchor for a second selected root over the first root's
stored algebraic values. Both descriptor validations and the nested sign and
zero queries occur inside the timed call. -/
def runNested : Unit → IO UInt64 := fun _ => do
  let some input ← rawRef.get
    | throw (IO.userError "nested benchmark: missing first descriptor")
  let some firstRoot := SignDet.Descriptor.validate Sturm.orderSign 7 input
    | throw (IO.userError "nested benchmark: first descriptor rejected")
  let first := Algebraic.Context.adjoin firstRoot (fun q : Rat => q.den == 1)
  let alpha := Algebraic.Element.ofPoly (context := first) x
  let y : DensePoly (Algebraic.Element first) := DensePoly.ofCoeffs #[0, 1]
  let raw : SignDet.RawDescriptor (Algebraic.Element first) Nat :=
    { context := 8, head := y * y - DensePoly.C alpha,
      lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  let some secondRoot := SignDet.Descriptor.validate Algebraic.Element.sign 8 raw
    | throw (IO.userError "nested benchmark: second descriptor rejected")
  let second := first.extend secondRoot
  let beta := Algebraic.Element.ofPoly (context := second) y
  let target := Algebraic.Element.ofCoeff (context := second) alpha
  if beta.sign == 1 && (beta * beta - target).sign == 0 &&
      (beta * beta⁻¹ - 1).sign == 0 then
    return 1
  else
    throw (IO.userError "nested benchmark: selected-value checks failed")

setup_fixed_benchmark runNested where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

/-- The exact ascending MetiTarski degree-15 input from CADE 2013, section 4.
The independent Phase4 oracle checks its least-root interval and root count. -/
private def metiCoefficients : Array Rat := #[592704, 402192, 90972, 3266731,
  -931392, -193914, -5792221, 756756, 140742, 3046158, -259308,
  -42336, -520884, 31752, 4536, 216]

private def metiHead : nativeBase.Poly :=
  DensePoly.ofCoeffs (metiCoefficients.map fun q => ⟨q⟩)

initialize metiRef : IO.Ref (Option nativeBase.Poly) ← IO.mkRef (some metiHead)

/-- Profile the actual first complete-root operation on the MetiTarski input.
The call checks the returned root count before returning its harness result. -/
def runMetiFirst : Unit → IO UInt64 := fun _ => do
  let some head ← metiRef.get | throw (IO.userError "missing MetiTarski first input")
  let .ok (.finite roots) := nativeBase.roots? head
    | throw (IO.userError "MetiTarski first root operation failed")
  unless roots.length == 3 do throw (IO.userError "MetiTarski first root count changed")
  return 1

setup_fixed_benchmark runMetiFirst where {
  repeats := 10, maxSecondsPerCall := 120.0, expectedHash := some 0x1
}

private instance : Hashable (Σ owner : Tower.Context nativeRegistry, owner.Poly) where
  hash input := hash (input.1.writePoly input.2).value

/-- Prepare the actual least-root coefficient context outside the measured
second-stage operation. Odd degrees extend `Y³ + α³ + 1` for a degree ladder;
rung three is the exact second MetiTarski input. -/
def metiSecondInput (degree : Nat) : Option (Σ owner : Tower.Context nativeRegistry, owner.Poly) :=
  match nativeBase.roots? metiHead with
  | .ok (.finite (first :: _)) =>
    if first.root.signAt (DensePoly.ofCoeffs #[⟨1875 / 2048⟩, 1]) != 1 ||
        first.root.signAt (DensePoly.ofCoeffs #[⟨1875 / 4096⟩, 1]) != -1 then none
    else
      let owner := first.root.context
      let alpha := first.root.value
      let y : owner.Poly := DensePoly.ofCoeffs #[0, 1]
      let power := (List.range degree).foldl (fun p _ => p * y) (DensePoly.C 1)
      some ⟨owner, power + DensePoly.C (alpha * alpha * alpha + 1)⟩
  | _ => none

/-- Complete native root production over the retained least-root context.
Preparation, hashing and process exit are outside the profile's timed regions. -/
def runMetiSecond (input : Option (Σ owner : Tower.Context nativeRegistry, owner.Poly)) : IO UInt64 := do
  let some ⟨owner, head⟩ := input
    | throw (IO.userError "MetiTarski second input preparation failed")
  let .ok (.finite roots) := owner.roots? head
    | throw (IO.userError "MetiTarski second root operation failed")
  unless roots.length == 1 do throw (IO.userError "MetiTarski second root count changed")
  return 1

setup_benchmark runMetiSecond n => n^3
  with prep := metiSecondInput
  where {
    paramFloor := 3, paramCeiling := 9
    paramSchedule := .custom #[3, 5, 7, 9]
    maxSecondsPerCall := 120.0
    targetInnerNanos := 500000000
    signalFloorMultiplier := 1.0
  }

end Hex.RealClosure.Bench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
