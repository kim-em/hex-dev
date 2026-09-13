/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexModularMatrix.Fixtures

/-! Integer determinant fixtures for the shared FLINT matrix oracle. -/

def main : IO Unit := do
  for c in Hex.ModularMatrixFixtures.cases do
    Hex.Conformance.Emit.emitMatrixFixture "HexModularMatrix" c.name
      (c.matrix.rows.toList.map (fun r => r.toList))
    Hex.Conformance.Emit.emitResult "HexModularMatrix" c.name "det"
      (toString (Hex.ModularMatrix.det c.matrix))
