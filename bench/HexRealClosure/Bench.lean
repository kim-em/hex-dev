/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealClosure.Element
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

end Hex.RealClosure.Bench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
