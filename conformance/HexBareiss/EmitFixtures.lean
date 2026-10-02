/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexBareiss.Fixtures

/-!
JSONL emit driver for the `hex-bareiss` oracle.

`lake exe hexbareiss_emit_fixtures` writes one `matrix` fixture record plus one
`bareiss` result record per case to `stdout` (or to `$HEX_FIXTURE_OUTPUT` when
set). The companion oracle driver `scripts/oracle/matrix_flint.py` reads the
same stream and re-runs the determinant through python-flint's `fmpz_mat.det`;
the fraction-free Bareiss algorithm is expected to agree with it on every
fixture.

Cases are square integer matrices at dimensions 4×4, 6×6, and 8×8 in three
structural shapes (`random/*`, `singular/*`, `triangular/*`); see the
`HexBareiss` Conformance module for the shape rationale. The single emitted
operation is `bareiss` (the executable fraction-free `Matrix.bareiss`).

Coordinate any future case-id additions with the sibling `HexDeterminant` and
`HexRowReduce` emit drivers so identical ids stay in sync.
-/

namespace Hex.BareissEmit

open Hex.Conformance.Emit
open Hex
open Hex.Matrix

private def lib : String := "HexBareiss"

private def matrixIntRows {n m : Nat} (M : Matrix Int n m) : List (List Int) :=
  M.rows.toList.map (fun row => row.toList)

private def jsonInt (n : Int) : String := toString n

/-- Emit one matrix fixture record plus its `bareiss` result record. -/
private def emitSquare (n : Nat) (id : String) (M : Matrix Int n n) : IO Unit := do
  emitMatrixFixture lib id (matrixIntRows M)
  emitResult lib id "bareiss" (jsonInt (Matrix.bareiss M))

private def emitAll : IO Unit := do
  emitSquare 4 "random/4x4"        random4
  emitSquare 4 "singular/4x4-def1" singular4Def1
  emitSquare 4 "singular/4x4-def2" singular4Def2
  emitSquare 4 "triangular/4x4"    triangular4
  emitSquare 6 "random/6x6"        random6
  emitSquare 6 "singular/6x6-def1" singular6Def1
  emitSquare 6 "triangular/6x6"    triangular6
  emitSquare 8 "random/8x8"        random8
  emitSquare 8 "triangular/8x8"    triangular8

end Hex.BareissEmit

def main : IO Unit :=
  Hex.BareissEmit.emitAll
