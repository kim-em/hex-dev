/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexModularMatrix.Fixtures

/-! Integer determinant fixtures for the shared FLINT matrix oracle. -/

open Hex Hex.Conformance.Emit

private def rows (A : Matrix Int n m) : String :=
  toString (A.rows.toList.map (·.toList))

private def solution (x : Option (Matrix Int n m × Int)) : String :=
  match x with
  | none => "null"
  | some (X, d) => "{\"num\":" ++ rows X ++ ",\"den\":" ++ toString d ++ "}"

private def emitSolve (name : String) (A : Matrix Int n n) (C : Matrix Int n m)
    (op : String) (answer : Option (Matrix Int n m × Int)) : IO Unit := do
  emitLine <| "{\"kind\":\"matrix\",\"lib\":\"HexModularMatrix\",\"case\":" ++
    toString (repr name) ++ ",\"rows\":" ++ rows A ++ ",\"rhs\":" ++ rows C ++
    ",\"rhsCols\":" ++ toString m ++ "}"
  emitResult "HexModularMatrix" name op (solution answer)

def main : IO Unit := do
  for c in ModularMatrixFixtures.cases do
    emitMatrixFixture "HexModularMatrix" c.name (c.matrix.rows.toList.map (·.toList))
    emitResult "HexModularMatrix" c.name "det" (toString (ModularMatrix.det c.matrix))
    for seed in [0, 1, 42] do
      emitResult "HexModularMatrix" c.name "det-divisor"
        (toString (ModularMatrix.detWith c.matrix (ModularMatrix.defaultFuel c.matrix) seed true).value)
    let A := c.matrix
    let b : Vector Int c.n := Vector.ofFn fun i => (i.val + 1 : Nat)
    let fuel := A.solveFuel + 2
    for (label, rhs) in [("rational", b), ("integral", A.mulVec b),
        ("zero", Vector.replicate c.n 0)] do
      let C : Matrix Int c.n 1 := Matrix.ofFn fun i _ => rhs[i]
      let answer := (A.solve? rhs fuel).map fun (y, d) =>
        (Matrix.ofFn (fun (i : Fin c.n) (_ : Fin 1) => y[i]), d)
      emitSolve (c.name ++ "/solve/" ++ label) A C "dixon-solve" answer
    for cols in ([0, 1, 3, c.n] : List Nat).eraseDups do
      let C : Matrix Int c.n cols := Matrix.ofFn fun i j => (i.val + j.val + 1 : Nat)
      let answer := (A.decomp? fuel).bind fun D => Matrix.solveMatWith D C
      emitSolve (c.name ++ "/repeated/" ++ toString cols) A C "dixon-solve" answer

  for c in ModularMatrixFixtures.rankCases do
    emitLine <| "{\"kind\":\"matrix\",\"lib\":\"HexModularMatrix\",\"case\":" ++
      toString (repr c.name) ++ ",\"rows\":" ++ rows c.matrix ++
      ",\"cols\":" ++ toString c.m ++ "}"
    emitResult "HexModularMatrix" c.name "rank" (toString c.matrix.rankModular)
    let some K := c.matrix.kernel? 3 | throw <| IO.userError ("kernel search failed: " ++ c.name)
    let basis := (List.finRange (c.m - K.cert.rank)).map fun j =>
      (List.finRange c.m).map fun i => [K.basis[(i, j)], K.cert.denom]
    emitResult "HexModularMatrix" c.name "nullspace" (toString basis)
