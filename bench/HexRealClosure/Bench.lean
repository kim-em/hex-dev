/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealClosure.Canonical
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
is a smoke safeguard, not a performance claim. -/
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

end Hex.RealClosure.Bench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
