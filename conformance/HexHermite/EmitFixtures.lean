/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexHermite

/-! JSONL fixtures for row Hermite normal form and its left transform. -/

namespace Hex.HermiteEmit

open Hex.Conformance.Emit
open Hex Matrix

private def lib := "HexHermite"

private def rows {n m : Nat} (M : Matrix Int n m) : List (List Int) :=
  M.rows.toList.map (fun row => row.toList)

private def jsonIntList (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

private def jsonMatrix {n m : Nat} (M : Matrix Int n m) : String :=
  "[" ++ String.intercalate "," ((rows M).map jsonIntList) ++ "]"

private def jsonTransform {n m : Nat} (H : Matrix Int n m)
    (U : Matrix Int n n) : String :=
  "{\"hnf\":" ++ jsonMatrix H ++ ",\"transform\":" ++ jsonMatrix U ++ "}"

private def emitCase {n m : Nat} (id : String) (A : Matrix Int n m) : IO Unit := do
  emitMatrixFixture lib id (rows A)
  emitResult lib id "hnf" (jsonMatrix (Matrix.hnf A))
  let D := Matrix.hnfData A
  emitResult lib id "hnf-transform" (jsonTransform D.echelon D.transform)

private def zero22 : Matrix Int 2 2 := 0
private def zeroLeft : Matrix Int 2 3 :=
  Matrix.ofFn fun i j => #[#[0, 4, 6], #[0, -2, 8]][i.val]![j.val]!
private def rankDeficient : Matrix Int 3 2 :=
  Matrix.ofFn fun i j => #[#[2, 4], #[-2, -4], #[4, 8]][i.val]![j.val]!
private def tall : Matrix Int 4 2 :=
  Matrix.ofFn fun i j => #[#[6, 9], #[4, 7], #[-2, 1], #[8, 14]][i.val]![j.val]!
private def wide : Matrix Int 2 4 :=
  Matrix.ofFn fun i j => #[#[-6, 9, -3, 12], #[4, -7, 5, -2]][i.val]![j.val]!
private def negativeLast : Matrix Int 2 2 :=
  Matrix.ofFn fun i j => if i = j then (if i.val = 0 then 1 else -1) else 0
private def alreadyHNF : Matrix Int 3 3 :=
  Matrix.ofFn fun i j => #[#[2, 1, 0], #[0, 3, 2], #[0, 0, 0]][i.val]![j.val]!
private def pivotOne : Matrix Int 3 3 :=
  Matrix.ofFn fun i j => #[#[3, -2, 7], #[2, -1, 4], #[5, -3, 11]][i.val]![j.val]!
private def negativePivots : Matrix Int 3 3 :=
  Matrix.ofFn fun i j =>
    #[#[-4, -6, -8], #[-2, -5, -7], #[-3, -1, -9]][i.val]![j.val]!
private def growth20 : Matrix Int 20 20 :=
  Matrix.ofFn fun i j =>
    Int.ofNat (((i.val + 1) * 37 + (j.val + 3) * 19 + 11) % 21) - 10

def emitAll : IO Unit := do
  emitCase "zero/2x2" zero22
  emitCase "zero-left/2x3" zeroLeft
  emitCase "rank-deficient/3x2" rankDeficient
  emitCase "tall/4x2" tall
  emitCase "wide/2x4" wide
  emitCase "negative-last/2x2" negativeLast
  emitCase "already-hnf/3x3" alreadyHNF
  emitCase "pivot-one/3x3" pivotOne
  emitCase "negative-pivots/3x3" negativePivots
  emitCase "growth/20x20" growth20

end Hex.HermiteEmit

def main : IO Unit := Hex.HermiteEmit.emitAll
