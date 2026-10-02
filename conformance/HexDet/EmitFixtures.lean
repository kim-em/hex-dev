/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexDet

/-!
JSONL emit driver for the `hex-det` scalar oracles.

`lake exe hexdet_emit_fixtures` writes one fixture record plus one dispatch
result per case to `stdout` (or to `$HEX_FIXTURE_OUTPUT` when set). The
companion driver `scripts/oracle/matrix_flint.py` re-runs each determinant
through python-flint: `fmpz_mat.det` for the integer cases, `fmpq_mat.det` for
the rational cases, and `nmod_mat.det` for the prime-residue cases.

Every emitted value is `Hex.Det.det`, so the oracle checks the answer dispatch
actually returns, not a lower algorithm called directly. Cases run at dimensions
4, 6 and 8 in the dense, singular and triangular shapes the sibling matrix emit
drivers use, so identical case ids stay comparable across libraries.

The polynomial and multivariate carriers are emitted separately by
`hexdet_emit_carrier_fixtures`, whose oracle is SymPy over the same exact
domains.
-/

namespace Hex.DetEmit

open Hex.Conformance.Emit
open Hex
open Hex.Det

private def lib : String := "HexDet"

scoped instance : ZMod64.Bounds 65521 := ⟨by decide, by decide⟩
scoped instance : ZMod64.PrimeModulus 65521 :=
  ZMod64.primeModulusOfPrime (by decide)

private abbrev Fp := ZMod64 65521

private def mkSquare {R : Type} [Zero R] (n : Nat) (rows : Array (Array R)) :
    Matrix R n n :=
  Matrix.ofFn fun i j => (rows.getD i.val #[]).getD j.val 0

private def matrixRows {R : Type} {n m : Nat} (M : Matrix R n m) : List (List R) :=
  M.rows.toList.map (fun row => row.toList)

/-- Emit one integer fixture and the determinant dispatch returns for it. -/
private def emitInt (n : Nat) (id : String) (M : Matrix Int n n) : IO Unit := do
  emitMatrixFixture lib id (matrixRows M)
  emitResult lib id "det" (toString (Hex.Det.det M))

/-- Emit one rational fixture and its dispatch determinant. -/
private def emitRat (n : Nat) (id : String) (M : Matrix Rat n n) : IO Unit := do
  emitRatMatrixFixture lib id (matrixRows M)
  emitResult lib id "det-rat" (ratValue (Hex.Det.det M))

/-- Emit one prime-residue fixture and its dispatch determinant. -/
private def emitMod (n : Nat) (id : String) (M : Matrix Fp n n) : IO Unit := do
  emitModMatrixFixture lib id 65521 ((matrixRows M).map fun row => row.map (·.toNat))
  emitResult lib id "det-mod" (toString (Hex.Det.det M).toNat)

private def random4 : Matrix Int 4 4 :=
  mkSquare 4 #[#[3, 1, 4, 1], #[5, 9, 2, 6], #[5, 3, 5, 8], #[9, 7, 9, 3]]

private def singular4 : Matrix Int 4 4 :=
  mkSquare 4 #[#[1, 2, 3, 4], #[2, 4, 6, 8], #[3, 3, 3, 3], #[5, 4, 3, 2]]

private def triangular4 : Matrix Int 4 4 :=
  mkSquare 4 #[#[2, 1, 4, 0], #[0, -3, 2, 1], #[0, 0, 5, 6], #[0, 0, 0, 7]]

private def pivot4 : Matrix Int 4 4 :=
  mkSquare 4 #[#[0, 1, 4, 1], #[0, 0, 2, 6], #[5, 3, 5, 8], #[9, 7, 9, 3]]

private def random6 : Matrix Int 6 6 :=
  mkSquare 6 #[
    #[ 3,  1, -2,  4,  0,  1],
    #[ 0,  5,  1, -1,  3,  2],
    #[ 2, -1,  4,  0,  1,  3],
    #[ 1,  2,  0,  3, -2,  4],
    #[-1,  0,  2,  1,  4,  0],
    #[ 4,  3,  1,  2, -3,  5]]

private def unimodular6 : Matrix Int 6 6 :=
  mkSquare 6 #[
    #[1, 2, 0, 0, 1, 3],
    #[0, 1, 4, 0, 0, 1],
    #[0, 0, 1, 2, 0, 0],
    #[0, 0, 0, 1, 5, 0],
    #[0, 0, 0, 0, 1, 2],
    #[0, 0, 0, 0, 0, 1]]

private def random8 : Matrix Int 8 8 :=
  mkSquare 8 #[
    #[ 2,  0,  1, -1,  3,  0,  4,  1],
    #[ 1,  3,  0,  2, -1,  4,  1,  0],
    #[ 0, -2,  3,  1,  4,  0,  2,  1],
    #[ 4,  1, -1,  2,  0,  3,  1,  2],
    #[-1,  2,  0,  1,  3,  1, -2,  4],
    #[ 3,  0,  2, -1,  1,  4,  0,  1],
    #[ 1,  4,  1,  0, -2,  2,  3,  0],
    #[ 0,  1,  3,  4,  1, -1,  2,  3]]

private def wideEntries6 : Matrix Int 6 6 :=
  mkSquare 6 #[
    #[ 1234567891011, -987654321, 4, 1, 0, 2],
    #[ 3, 2718281828459045, 1, -4, 2, 0],
    #[ 0, 1, 3141592653589793, 2, 1, 5],
    #[ 2, 0, 1, -1618033988749895, 3, 1],
    #[ 1, 3, 0, 2, 5772156649015329, 1],
    #[ 4, 1, 2, 0, 1, -1414213562373095]]

private def ratOf (num den : Int) : Rat := (num : Rat) / (den : Rat)

private def random4Rat : Matrix Rat 4 4 :=
  mkSquare 4 #[
    #[ratOf 1 2, ratOf 2 3, ratOf 3 5, ratOf 1 7],
    #[ratOf 5 3, ratOf 1 4, ratOf 2 9, ratOf 6 5],
    #[ratOf 5 6, ratOf 3 7, ratOf 5 2, ratOf 8 3],
    #[ratOf 9 4, ratOf 7 5, ratOf 9 8, ratOf 3 2]]

private def singular4Rat : Matrix Rat 4 4 :=
  mkSquare 4 #[
    #[ratOf 1 2, ratOf 1 1, ratOf 3 2, ratOf 2 1],
    #[ratOf 1 1, ratOf 2 1, ratOf 3 1, ratOf 4 1],
    #[ratOf 3 4, ratOf 1 3, ratOf 5 6, ratOf 1 5],
    #[ratOf 5 2, ratOf 4 3, ratOf 1 6, ratOf 7 5]]

private def random6Rat : Matrix Rat 6 6 :=
  mkSquare 6 #[
    #[ratOf 3 2, ratOf 1 3, ratOf (-2) 5, ratOf 4 7, ratOf 0 1, ratOf 1 4],
    #[ratOf 0 1, ratOf 5 3, ratOf 1 2, ratOf (-1) 6, ratOf 3 5, ratOf 2 9],
    #[ratOf 2 7, ratOf (-1) 4, ratOf 4 3, ratOf 0 1, ratOf 1 8, ratOf 3 2],
    #[ratOf 1 5, ratOf 2 3, ratOf 0 1, ratOf 3 4, ratOf (-2) 7, ratOf 4 5],
    #[ratOf (-1) 2, ratOf 0 1, ratOf 2 5, ratOf 1 3, ratOf 4 9, ratOf 0 1],
    #[ratOf 4 3, ratOf 3 8, ratOf 1 6, ratOf 2 5, ratOf (-3) 4, ratOf 5 7]]

private def modOf (z : Int) : Fp := (z : Fp)

private def random4Mod : Matrix Fp 4 4 :=
  mkSquare 4 (#[#[3, 1, 4, 1], #[5, 9, 2, 6], #[5, 3, 5, 8], #[9, 7, 9, 3]].map
    (fun row => row.map (fun z : Int => modOf (z * 271828))))

private def singular4Mod : Matrix Fp 4 4 :=
  mkSquare 4 (#[#[1, 2, 3, 4], #[2, 4, 6, 8], #[3, 3, 3, 3], #[5, 4, 3, 2]].map
    (fun row => row.map (fun z : Int => modOf (z * 31415))))

private def random6Mod : Matrix Fp 6 6 :=
  mkSquare 6 (#[
    #[ 3,  1, -2,  4,  0,  1],
    #[ 0,  5,  1, -1,  3,  2],
    #[ 2, -1,  4,  0,  1,  3],
    #[ 1,  2,  0,  3, -2,  4],
    #[-1,  0,  2,  1,  4,  0],
    #[ 4,  3,  1,  2, -3,  5]].map
    (fun row => row.map (fun z : Int => modOf (z * 161803))))

private def emitAll : IO Unit := do
  emitInt 4 "random/4x4"      random4
  emitInt 4 "singular/4x4"    singular4
  emitInt 4 "triangular/4x4"  triangular4
  emitInt 4 "pivot/4x4"       pivot4
  emitInt 6 "random/6x6"      random6
  emitInt 6 "unimodular/6x6"  unimodular6
  emitInt 6 "wide/6x6"        wideEntries6
  emitInt 8 "random/8x8"      random8
  emitRat 4 "rat-random/4x4"   random4Rat
  emitRat 4 "rat-singular/4x4" singular4Rat
  emitRat 6 "rat-random/6x6"   random6Rat
  emitMod 4 "mod-random/4x4"   random4Mod
  emitMod 4 "mod-singular/4x4" singular4Mod
  emitMod 6 "mod-random/6x6"   random6Mod

end Hex.DetEmit

def main : IO Unit :=
  Hex.DetEmit.emitAll
