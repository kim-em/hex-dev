/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexCharPoly.Fixtures

/-! JSONL emission for the python-flint characteristic-polynomial oracle. -/

namespace Hex.CharPolyEmit

open Hex.Conformance.Emit

private def rows (c : Hex.CharPolyFixtures.Case) : List (List Int) :=
  c.matrix.rows.toList.map Vector.toList

private def emitCase (c : Hex.CharPolyFixtures.Case) : IO Unit := do
  emitMatrixFixture "HexCharPoly" c.id (rows c)
  emitResult "HexCharPoly" c.id "charpoly"
    (intListValue c.matrix.charPoly.toArray.toList)

def emitAll : IO Unit :=
  Hex.CharPolyFixtures.all.forM emitCase

end Hex.CharPolyEmit

def main : IO Unit := Hex.CharPolyEmit.emitAll
