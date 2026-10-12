/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealClosure.Trivial
import LeanBench
import Lean.Data.Json

namespace Hex.RealClosure.TrivialMeasurements

structure Input where
  index : Nat
  polynomial : DensePoly Rat
  canonical : RealAlgebraicPoly
  multiplicity : Nat

inductive Method where
  | generic | canonical

private def Method.label : Method → String
  | .generic => "generic"
  | .canonical => "canonical"

private def prepare (index : Nat) : Input :=
  let multiplicity := if index < 2 then 0 else 2 ^ (index - 2)
  let quadratic : DensePoly Rat := DensePoly.ofCoeffs #[-2, 0, 1]
  let polynomial := if index == 0 then 0 else if index == 1 then DensePoly.C 5
    else (List.range multiplicity).foldl (fun p _ => p * quadratic) 1
  ⟨index, polynomial, Trivial.Rational.polynomial polynomial, multiplicity⟩

initialize inputs : IO.Ref (Option (Array Input)) ← IO.mkRef none

def install : IO Unit := inputs.set (some ((List.range 6).toArray.map prepare))

private def getInput (index : Nat) : IO Input := do
  let some prepared ← inputs.get | throw (IO.userError "trivial inputs are not installed")
  let some input := prepared[index]? | throw (IO.userError "trivial input index is not registered")
  return input

/-- The generic route includes checked generic isolation and conversion of each
selected descriptor. The canonical arm uses the existing complete backend. -/
def roots (input : Input) : Method → RealRootSet
  | .generic => Trivial.Rational.roots 10378 input.polynomial
  | .canonical => input.canonical.roots

/-- Force the complete result, root order, exact square identities and Yun
multiplicities, retaining the zero polynomial's distinct `all` result. -/
def check (input : Input) : RealRootSet → Bool
  | .all => input.index == 0
  | .finite values =>
    if input.index == 1 then values.isEmpty
    else if input.index < 2 then false
    else match values.toList with
      | [lower, upper] =>
        lower.multiplicity == input.multiplicity && upper.multiplicity == input.multiplicity &&
        RealAlgebraicNumber.compare lower.root upper.root == .lt &&
        lower.root.sign == -1 && upper.root.sign == 1 &&
        lower.root * lower.root == RealAlgebraicNumber.ofRat 2 &&
        upper.root * upper.root == RealAlgebraicNumber.ofRat 2
      | _ => false

/-- The timing includes complete root construction and the common exact
consumer; input construction and rational-to-canonical lifting are outside. -/
def measure (index : Nat) (method : Method) (_ : Unit) : IO UInt64 := do
  let input ← getInput index
  unless check input (roots input method) do throw (IO.userError "trivial result mismatch")
  return 1

namespace Zero

def generic := measure 0 .generic
def canonical := measure 0 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Zero

namespace Constant

def generic := measure 1 .generic
def canonical := measure 1 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Constant

namespace Multiplicity1

def generic := measure 2 .generic
def canonical := measure 2 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Multiplicity1

namespace Multiplicity2

def generic := measure 3 .generic
def canonical := measure 3 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Multiplicity2

namespace Multiplicity4

def generic := measure 4 .generic
def canonical := measure 4 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Multiplicity4

namespace Multiplicity8

def generic := measure 5 .generic
def canonical := measure 5 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Multiplicity8

private def rat (value : Rat) : Lean.Json := Lean.toJson [value.num, (value.den : Int)]

/-- Serialize exact rational inputs and canonical root presentations separately
from timing. The independent oracle verifies exact roots and multiplicities. -/
def emit : IO Unit := do
  for index in List.range 6 do
    let input ← getInput index
    for method in [Method.generic, .canonical] do
      let result := roots input method
      unless check input result do throw (IO.userError "trivial functional result mismatch")
      let output := match result with
        | .all => Lean.Json.null
        | .finite values => Lean.Json.arr (values.map fun value =>
          let square := value.root.toAlgebraic.rep.1.square
          Lean.Json.mkObj [
            ("polynomial", Lean.toJson value.root.toAlgebraic.p.toArray),
            ("re", rat square.re.toRat), ("im", rat square.im.toRat),
            ("precision", Lean.toJson square.prec),
            ("sign", Lean.toJson value.root.sign),
            ("multiplicity", Lean.toJson value.multiplicity)])
      IO.println <| (Lean.Json.mkObj [
        ("index", Lean.toJson index), ("method", Lean.toJson method.label),
        ("coefficients", Lean.Json.arr (input.polynomial.toArray.map rat)),
        ("multiplicity", Lean.toJson input.multiplicity), ("roots", output)]).compress

end Hex.RealClosure.TrivialMeasurements

def main (args : List String) : IO UInt32 := do
  Hex.RealClosure.TrivialMeasurements.install
  if args.isEmpty || args == ["emit"] then
    Hex.RealClosure.TrivialMeasurements.emit
    return 0
  LeanBench.Cli.dispatch args
