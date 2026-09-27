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

/-- Functional timing anchor for polynomial division over packed coefficients.
The input is `(Y - √2)(Y + √2)` divided by `Y - √2`, with the selected root
from the test polynomial. The ten-second cap is an operational safeguard. -/
def runPoly : Unit → IO UInt64 := fun _ => do
  let some input ← rawRef.get
    | throw (IO.userError "polynomial benchmark: missing input")
  let some d := Root.validate 7 input
    | throw (IO.userError "polynomial benchmark: descriptor rejected")
  let alpha : Element d := Element.ofPoly x
  let y : DensePoly (Element d) := DensePoly.ofCoeffs #[0, 1]
  let divisor := y - DensePoly.C alpha
  let dividend := divisor * (y + DensePoly.C alpha)
  let (quotient, remainder) := DensePoly.divMod dividend divisor
  if remainder.isZero && quotient.natDegree == 1 &&
      Element.equal (quotient.eval (0 : Element d)) alpha then
    return 1
  else
    throw (IO.userError "polynomial benchmark: wrong quotient or remainder")

setup_fixed_benchmark runPoly where {
  repeats := 10, maxSecondsPerCall := 10.0, expectedHash := some 0x1
}

end Hex.RealClosure.Bench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
