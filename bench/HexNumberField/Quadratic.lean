/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexNumberField
open Hex

/-! Compiled stage decomposition and resource regression for issue #10156.
Run under a process-tree memory/CPU cap; see reports/hex-number-field-quadratic.md.
The height and stage are runtime arguments, and every result is consumed. -/

def main (args : List String) : IO Unit := do
  let height := (args[1]?.getD "20").toNat!
  let n : Int := 2 ^ height
  let p : ZPoly := DensePoly.ofList [(n+1)^2, 0, n^2]
  let stage := args[0]?.getD "canonical"
  IO.println s!"stage={stage} height={height} p={repr p}"
  (← IO.getStdout).flush
  match stage with
  | "squarefree" => IO.println s!"{repr (ZPoly.squareFreeCore p)}"
  | "factor" => IO.println s!"{repr (ZPoly.factorize p).factors}"
  | "isolate" =>
    if h : HasOnlySimpleRoots p then
      let rs := ZPoly.isolateComplexRoots? p h (separationDepth p : Int)
      IO.println s!"{repr (rs.map (·.map (·.square.prec)))}"
    else throw (IO.userError "not squarefree")
  | "arithmetic" =>
    let upper := (1 + AlgebraicNumber.ofRat (1 / (n : Rat))) * AlgebraicNumber.I
    IO.println s!"{repr upper.p}"
  | "regression" =>
    let rs := p.algebraicRoots
    let upper := (1 + AlgebraicNumber.ofRat (1 / (n : Rat))) * AlgebraicNumber.I
    unless rs == #[-upper, upper] && rs.all (fun r => r.p == p) do
      throw (IO.userError "quadratic canonical equality failed")
    IO.println "quadratic canonical and arithmetic construction agree"
  | "canonical" =>
    let rs := p.algebraicRoots
    IO.println s!"{repr (rs.map fun r => (r.p.toArray, r.isReal))}"
  | _ => throw (IO.userError s!"unknown stage: {stage}")
