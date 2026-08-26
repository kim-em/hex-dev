/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexBareiss.Bareiss

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

/-- Build a square `Matrix Int n n` from a 2-D array of rows; missing entries
default to `0`. -/
private def mkSquare (n : Nat) (rows : Array (Array Int)) : Matrix Int n n :=
  Matrix.ofFn fun i j =>
    (rows.getD i.val #[]).getD j.val 0

private def random4 : Matrix Int 4 4 :=
  mkSquare 4 #[#[3, 1, 4, 1], #[5, 9, 2, 6], #[5, 3, 5, 8], #[9, 7, 9, 3]]

private def singular4Def1 : Matrix Int 4 4 :=
  mkSquare 4 #[#[2, 0, -1, 3], #[1, 5, 4, -2], #[0, 3, 7, 1],
               #[3, 5, 3, 1]]

private def singular4Def2 : Matrix Int 4 4 :=
  mkSquare 4 #[#[1, 2, 3, 4], #[2, 1, 0, -1],
               #[3, 3, 3, 3], #[5, 4, 3, 2]]

private def triangular4 : Matrix Int 4 4 :=
  mkSquare 4 #[#[2, 1, 4, 0], #[0, -3, 2, 1], #[0, 0, 5, 6], #[0, 0, 0, 7]]

private def random6 : Matrix Int 6 6 :=
  mkSquare 6 #[
    #[ 3,  1, -2,  4,  0,  1],
    #[ 0,  5,  1, -1,  3,  2],
    #[ 2, -1,  4,  0,  1,  3],
    #[ 1,  2,  0,  3, -2,  4],
    #[-1,  0,  2,  1,  4,  0],
    #[ 4,  3,  1,  2, -3,  5]
  ]

private def singular6Def1 : Matrix Int 6 6 :=
  mkSquare 6 #[
    #[ 1,  2,  3, -1,  0,  4],
    #[ 0,  1, -2,  3,  1,  2],
    #[ 4, -1,  0,  2,  3,  1],
    #[ 2,  3,  1,  0,  4, -1],
    #[ 1,  0,  4,  3, -2,  2],
    #[ 1,  3,  1,  2,  1,  6]   -- = row0 + row1
  ]

private def triangular6 : Matrix Int 6 6 :=
  mkSquare 6 #[
    #[1,  2, -1,  3,  0,  1],
    #[0,  2,  4, -2,  1,  3],
    #[0,  0,  3,  1,  2, -1],
    #[0,  0,  0,  4,  0,  2],
    #[0,  0,  0,  0,  5,  3],
    #[0,  0,  0,  0,  0,  6]
  ]

private def random8 : Matrix Int 8 8 :=
  mkSquare 8 #[
    #[ 2,  0,  1, -1,  3,  0,  4,  1],
    #[ 1,  3,  0,  2, -1,  4,  1,  0],
    #[ 0, -2,  3,  1,  4,  0,  2,  1],
    #[ 4,  1, -1,  2,  0,  3,  1,  2],
    #[-1,  2,  0,  1,  3,  1, -2,  4],
    #[ 3,  0,  2, -1,  1,  4,  0,  1],
    #[ 1,  4,  1,  0, -2,  2,  3,  0],
    #[ 0,  1,  3,  4,  1, -1,  2,  3]
  ]

private def triangular8 : Matrix Int 8 8 :=
  mkSquare 8 #[
    #[1, 2, 0, 1, 3, -1, 0, 2],
    #[0, 1, 3, -2, 0, 1, 4, 0],
    #[0, 0, 2, 1, -1, 0, 3, 1],
    #[0, 0, 0, 2, 0, 4, -1, 0],
    #[0, 0, 0, 0, 3, 1, 0, 2],
    #[0, 0, 0, 0, 0, 3, 2, -1],
    #[0, 0, 0, 0, 0, 0, 4, 1],
    #[0, 0, 0, 0, 0, 0, 0, 4]
  ]

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
