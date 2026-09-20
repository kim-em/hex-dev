/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
import HexRealAlgebraic.Roots

open Hex

namespace CadSampleCosts

private def polyInfo (p : ZPoly) : String :=
  ("{" ++ s!"\"degree\":{p.natDegree},\"height\":{p.coeffAbsMax},\"coefficients\":{repr p.toArray.toList}" ++ "}")

private def numbersInfo (xs : Array RealAlgebraicNumber) : String :=
  "[" ++ String.intercalate "," (xs.toList.map fun a => polyInfo a.toAlgebraic.p) ++ "]"

@[noinline] private def baseRoots (p : ZPoly) : Array RealAlgebraicNumber :=
  p.realAlgebraicRoots

@[noinline] private def liftRoots (coeffs : Array RealAlgebraicNumber) : Array RealAlgebraicNumber :=
  (RealAlgebraicPoly.ofArray coeffs).roots.toArray.map (·.root)

@[noinline] private def runThunk (f : Unit → α) : IO α :=
  pure (f ())

private def timeRoots (name : String) (level : Nat) (operation : String)
    (input : String) (f : Unit → Array RealAlgebraicNumber) : IO (Array RealAlgebraicNumber) := do
  let start ← IO.monoNanosNow
  let result ← runThunk f
  -- The output is consumed below; elapsed time excludes formatting.
  let stop ← IO.monoNanosNow
  IO.println ("{" ++ s!"\"example\":\"{name}\",\"level\":{level},\"operation\":\"{operation}\",\"input\":{input},\"ns\":{stop-start},\"roots\":{numbersInfo result}" ++ "}")
  (← IO.getStdout).flush
  if result.isEmpty then throw (IO.userError "expected finite nonempty roots")
  return result

private def timeCoeffs (name : String) (level : Nat)
    (f : Unit → Array RealAlgebraicNumber) : IO (Array RealAlgebraicNumber) := do
  let start ← IO.monoNanosNow
  let result ← runThunk f
  let stop ← IO.monoNanosNow
  IO.println ("{" ++ s!"\"example\":\"{name}\",\"level\":{level},\"operation\":\"substitution\",\"ns\":{stop-start},\"coefficients\":{numbersInfo result}" ++ "}")
  (← IO.getStdout).flush
  return result

private def run (name : String) : IO Unit := do
  let p : ZPoly ← match name with
    | "nlsat" => pure #p[16, 1, -8, 16]
    | "circle-parabola" => pure #p[-1, 0, 1, 0, 1]
    | "circles" => pure #p[-1, 2]
    | "kahan" => pure #p[-1, -8, 16]
    | "sphere" => pure #p[-1, 0, 2]
    | "tower4" => pure #p[-2, 0, 1]
    | "tower8" => pure #p[-2, 0, 0, 0, 1]
    | _ => throw (IO.userError s!"unknown example {name}")
  let first ← timeRoots name 1 "ZPoly.realAlgebraicRoots" (polyInfo p) fun _ => baseRoots p
  let a := if name == "nlsat" then first[0]! else first[first.size - 1]!
  let one := RealAlgebraicNumber.ofRat 1
  let zero := RealAlgebraicNumber.zero
  let eight := RealAlgebraicNumber.ofRat 8
  let sixteen := RealAlgebraicNumber.ofRat 16
  let three := RealAlgebraicNumber.ofRat 3
  let sixtyFour := RealAlgebraicNumber.ofRat 64
  let fiveSixths := RealAlgebraicNumber.ofRat (5/6)
  let coeffs ← timeCoeffs name 2 fun _ =>
    if name == "tower4" || name == "tower8" then #[-a, zero, one]
    else if name == "kahan" then #[(sixteen * a^2 - eight*a - three) / sixtyFour, zero, one]
    else if name == "sphere" then #[a^2 - fiveSixths, zero, one]
    else #[a^2 - one, zero, one]
  let second ← timeRoots name 2 "RealAlgebraicPoly.roots" (numbersInfo coeffs) fun _ => liftRoots coeffs
  let b := if name == "nlsat" then second[0]! else second[second.size - 1]!
  if name == "sphere" then
    let coeffs ← timeCoeffs name 3 fun _ => #[a^2 + b^2 - one, zero, one]
    let _ ← timeRoots name 3 "RealAlgebraicPoly.roots" (numbersInfo coeffs) fun _ => liftRoots coeffs
    pure ()
  -- Keep the selected tuple in the raw record, separately from all lifted roots.
  IO.println ("{" ++ s!"\"example\":\"{name}\",\"sample\":{numbersInfo #[a,b]}" ++ "}")

end CadSampleCosts

public def main (args : List String) : IO Unit := do
  match args with
  | [name] => CadSampleCosts.run name
  | _ => throw (IO.userError "usage: cad_sample_costs EXAMPLE")
