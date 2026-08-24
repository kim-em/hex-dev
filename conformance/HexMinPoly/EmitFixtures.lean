/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexMinPoly.Fixtures

namespace Hex.MinPolyEmit

open Hex.Conformance.Emit

private def rows (c : Hex.MinPolyFixtures.Case) : List (List Int) :=
  c.matrix.rows.toList.map Vector.toList

private def intToRat {n m : Nat} (M : Matrix Int n m) : Matrix Rat n m :=
  Matrix.ofRows (M.rows.map (fun row => row.map (fun x => ((x : Int) : Rat))))

private def emitCase (c : Hex.MinPolyFixtures.Case) : IO Unit := do
  emitMatrixFixture "HexMinPoly" c.id (rows c)
  let answer := Matrix.minPoly (intToRat c.matrix)
  emitResult "HexMinPoly" c.id "minpoly"
    (intListValue (answer.toArray.toList.map (fun q => q.num)))

def emitAll : IO Unit := Hex.MinPolyFixtures.all.forM emitCase

end Hex.MinPolyEmit

def main : IO Unit := Hex.MinPolyEmit.emitAll
