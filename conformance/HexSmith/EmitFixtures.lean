/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexSmith
import HexMatrix.Notation

/-! JSONL fixtures for the canonical Smith diagonal. -/

namespace Hex.SmithEmit

open Hex.Conformance.Emit
open Hex Matrix

private def lib := "HexSmith"

private def rows {n m : Nat} (M : Matrix Int n m) : List (List Int) :=
  M.rows.toList.map (fun row => row.toList)

private def jsonIntList (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

private def jsonMatrix {n m : Nat} (M : Matrix Int n m) : String :=
  "[" ++ String.intercalate "," ((rows M).map jsonIntList) ++ "]"

private def emitCase {n m : Nat} (id : String) (A : Matrix Int n m) : IO Unit := do
  emitMatrixFixture lib id (rows A)
  emitResult lib id "snf" (jsonMatrix (Matrix.snf A))

private def empty00 : Matrix Int 0 0 := 0
private def empty03 : Matrix Int 0 3 := 0
private def empty30 : Matrix Int 3 0 := 0
private def zero22 : Matrix Int 2 2 := 0
private def rankOne : Matrix Int 3 2 :=
  Matrix.ofFn fun i j => #[#[2, 4], #[-2, -4], #[4, 8]][i.val]![j.val]!
private def coprimeDiagonal : Matrix Int 2 2 :=
  Matrix.ofFn fun i j => #[#[2, 0], #[0, 3]][i.val]![j.val]!
private def chainConjugate : Matrix Int 3 3 :=
  Matrix.ofFn fun i j => #[#[2, 2, 0], #[0, 4, 4], #[0, 0, 8]][i.val]![j.val]!
private def rankDeficient : Matrix Int 3 3 :=
  Matrix.ofFn fun i j => #[#[2, 4, 6], #[1, 2, 3], #[0, 0, 0]][i.val]![j.val]!
private def tall : Matrix Int 3 2 :=
  Matrix.ofFn fun i j => #[#[6, 9], #[4, 7], #[-2, 1]][i.val]![j.val]!
private def wide : Matrix Int 2 3 :=
  Matrix.ofFn fun i j => #[#[6, 4, -2], #[9, 7, 1]][i.val]![j.val]!
private def mixed : Matrix Int 2 2 :=
  Matrix.ofFn fun i j => #[#[-4, 6], #[10, -14]][i.val]![j.val]!
private def minusOne : Matrix Int 1 1 :=
  Matrix.ofFn fun _ _ => -1
private def negativeLast : Matrix Int 2 2 :=
  Matrix.ofFn fun i j => if i = j then (if i.val = 0 then 1 else -2) else 0
private def group22 : Matrix Int 2 2 :=
  Matrix.ofFn fun i j => if i = j then 2 else 0
private def group2 : Matrix Int 2 2 :=
  Matrix.ofFn fun i j => #[#[1, 1], #[0, 2]][i.val]![j.val]!
private def leftSix : Matrix Int 6 6 :=
  #m[1, 1, 0, 0, 0, 0;
     0, 1, 1, 0, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]
private def diagonalSix : Matrix Int 6 6 :=
  #m[1, 0, 0, 0, 0, 0;
     0, 2, 0, 0, 0, 0;
     0, 0, 6, 0, 0, 0;
     0, 0, 0, 12, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]
private def rightSix : Matrix Int 6 6 :=
  #m[1, 0, 0, 0, 0, 0;
     1, 1, 0, 0, 0, 0;
     0, 1, 1, 0, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 1, 1]
private def conjugateSix : Matrix Int 6 6 := leftSix * diagonalSix * rightSix

def emitAll : IO Unit := do
  emitCase "empty/0x0" empty00
  emitCase "empty/0x3" empty03
  emitCase "empty/3x0" empty30
  emitCase "zero/2x2" zero22
  emitCase "rank-one/3x2" rankOne
  emitCase "coprime-diagonal/2x2" coprimeDiagonal
  emitCase "chain-conjugate/3x3" chainConjugate
  emitCase "rank-deficient/3x3" rankDeficient
  emitCase "tall/3x2" tall
  emitCase "wide/2x3" wide
  emitCase "mixed-sign/2x2" mixed
  emitCase "minus-one/1x1" minusOne
  emitCase "negative-last/2x2" negativeLast
  emitCase "group-z2-z2/2x2" group22
  emitCase "group-z2/2x2" group2
  emitCase "chain-conjugate/6x6" conjugateSix

end Hex.SmithEmit

def main : IO Unit := Hex.SmithEmit.emitAll
