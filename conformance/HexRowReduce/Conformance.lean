/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRowReduce
import HexRowReduce.Witness
import HexRowReduce.FieldFixtures

/-!
Core conformance checks for `hex-row-reduce`.

Run this file through the conformance Lake target, not direct `lake env lean`.

Oracle: `scripts/oracle/matrix_flint.py` (`rank` / `rowReduce` / `nullspace` ops,
via the `hexrowreduce_emit_fixtures` stream)
Mode: always
Covered operations:
- row reduction and span APIs (`rowReduce`, `rowReduce_rank`, `spanCoeffs`,
  `vecMul`, `spanContains`)
- nullspace basis extraction (`nullspace`, `nullspaceBasisMatrix`)
- field inverse, complete solve, and the option view (`inverse?`, `solve`, `solve?`)
- canonical particular solutions, bases, and separating witnesses for Rat,
  characteristic two, an odd prime, and rational functions; exact FLINT/SymPy
  oracle checks include full solution-space dimension and empty shapes
Covered properties:
- `rowReduce` returns data whose transform matrix multiplies the input to the
  reported echelon form
- `spanCoeffs` witnesses row-span membership on a committed dependent-row example
- the committed nullspace basis vectors are annihilated by the source matrix
Covered edge cases:
- zero matrices, full-rank systems, dependent rows producing nontrivial span and
  nullspace behaviour, and empty pivot-column / empty nullspace outputs
-/

namespace Hex

namespace Matrix

private def dependentRat : Matrix Rat 2 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 2
    | 0, _ => 3
    | 1, 0 => 2
    | 1, 1 => 4
    | _, _ => 6

private def dependentRowReduced : Matrix Rat 2 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 2
    | 0, _ => 3
    | _, _ => 0

private def zeroRat23 : Matrix Rat 2 3 := 0

private def fullRat22 : Matrix Rat 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, _ => 2
    | 1, 0 => 3
    | _, _ => 5

private def spanVec : Vector Rat 3 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 1
    | 1 => 2
    | _ => 3

private def offSpanVec : Vector Rat 3 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 1
    | 1 => 0
    | _ => 0

private def zeroRat3 : Vector Rat 3 := Vector.ofFn fun _ => 0

private def zeroRat2 : Vector Rat 2 := Vector.ofFn fun _ => 0

private def spanCoeffsWitness : Vector Rat 2 :=
  Vector.ofFn fun i => if i.val = 0 then 1 else 0

private def dependentNullspace : Vector (Vector Rat 3) 2 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => Vector.ofFn fun j =>
        match j.val with
        | 0 => -2
        | 1 => 1
        | _ => 0
    | _ => Vector.ofFn fun j =>
        match j.val with
        | 0 => -3
        | 1 => 0
        | _ => 1

private def zeroNullspace : Vector (Vector Rat 3) 3 :=
  Vector.ofFn fun i =>
    Vector.ofFn fun j => if i = j then 1 else 0

private def emptyNullspace : Vector (Vector Rat 2) 0 :=
  Vector.ofFn fun i => nomatch i

/- RREF, span, and nullspace executable conformance guards. -/

#guard let D := Matrix.rowReduce dependentRat; D.rank = 1
#guard let D := Matrix.rowReduce dependentRat; D.echelon = dependentRowReduced
#guard let D := Matrix.rowReduce dependentRat; D.transform * dependentRat = D.echelon
#guard let D := Matrix.rowReduce zeroRat23; D.rank = 0
#guard let D := Matrix.rowReduce zeroRat23; D.pivotCols = Vector.ofFn (fun i => nomatch i)
#guard let D := Matrix.rowReduce fullRat22; D.rank = 2
#guard let D := Matrix.rowReduce fullRat22; D.echelon = (Matrix.identity (R := Rat) 2)

#guard Matrix.spanCoeffs dependentRat spanVec = some spanCoeffsWitness
#guard Matrix.vecMul spanCoeffsWitness dependentRat = spanVec
#guard Matrix.spanContains dependentRat spanVec
#guard Matrix.spanCoeffs dependentRat offSpanVec = none
#guard !(Matrix.spanContains dependentRat offSpanVec)
#guard Matrix.spanCoeffs zeroRat23 zeroRat3 = some zeroRat2

#guard (Matrix.nullspace dependentRat).toArray = dependentNullspace.toArray
#guard (Matrix.nullspace zeroRat23).toArray = zeroNullspace.toArray
#guard (Matrix.nullspace fullRat22).toArray = emptyNullspace.toArray
#guard dependentRat * dependentNullspace.get ⟨0, by decide⟩ = 0
#guard dependentRat * dependentNullspace.get ⟨1, by decide⟩ = 0

/- RREF, span, and nullspace proof-mode automation examples. -/

section RowReduceWrapperAutomation

example (M : Matrix Rat n m) (v : Vector Rat m) (c : Vector Rat n) :
    Matrix.spanCoeffs M v = some c → Matrix.vecMul c M = v := by
  exact Matrix.spanCoeffs_sound M v c

example (M : Matrix Rat n m) (v : Vector Rat m) :
    Matrix.spanContains M v = (Matrix.spanCoeffs M v).isSome := by
  simp

example (M : Matrix Rat n m) (v : Vector Rat m) :
    Matrix.spanContains M v = true →
      ∃ c : Vector Rat n, Matrix.vecMul c M = v := by
  exact (Matrix.spanContains_iff M v).mp

example (M : Matrix Rat n m) (k : Fin (m - Matrix.rowReduce_rank M)) :
    M * (Matrix.nullspace M).get k = 0 := by
  grind

example (M : Matrix Rat n m) (k : Fin (m - Matrix.rowReduce_rank M)) :
    Matrix.col (Matrix.nullspaceBasisMatrix M) k = (Matrix.nullspace M).get k := by
  grind

end RowReduceWrapperAutomation

end Matrix

open scoped Hex.RowReduceFixtures in
#guard (Hex.RowReduceFixtures.cases (1/2 : Rat)).all Hex.RowReduceFixtures.check

open scoped Hex.RowReduceFixtures in
#guard (Hex.RowReduceFixtures.cases (1 : Hex.ZMod64 2)).all Hex.RowReduceFixtures.check

open scoped Hex.RowReduceFixtures in
#guard (Hex.RowReduceFixtures.cases (3 : Hex.ZMod64 101)).all Hex.RowReduceFixtures.check

#guard (Hex.RowReduceFixtures.cases Hex.RowReduceFixtures.rationalFunction).all
  Hex.RowReduceFixtures.check

namespace Matrix.CertificateTests

open Lists

private def inverseInput : ScaledRows := ⟨1, [[1, 2], [2, 4]]⟩
private def singular : InverseWitness := .singular inverseInput ⟨1, [-2, 1]⟩ 1

#guard checkInverseList 2 [[1, 2], [2, 4]] singular
#guard !checkInverseList 2 [[1, 2], [2, 4]] (.singular inverseInput ⟨1, [0, 0]⟩ 1)
#guard !checkInverseList 2 [[1, 2], [2, 4]] (.singular inverseInput ⟨1, [-2, 1]⟩ 2)
#guard !checkInverseList 2 [[1, 2], [2, 4]] (.singular inverseInput ⟨0, [-2, 1]⟩ 1)
#guard !checkInverseList 2 [[1, 2], [2, 4]] (.singular inverseInput ⟨1, [-1, 1]⟩ 1)
#guard !checkInverseList 2 [[1, 2], [2, 4]] (.singular inverseInput ⟨1, [-2]⟩ 0)
#guard !checkInverseList 1 [[2]] (.invertible ⟨1, [[2]]⟩ ⟨1, [[1]]⟩)
#guard !checkInverseList 1 [[2]] (.invertible ⟨1, [[2]]⟩ ⟨0, [[1]]⟩)
#guard !checkInverseList 1 [[2]] (.invertible ⟨0, [[2]]⟩ ⟨2, [[1]]⟩)
#guard !checkInverseList 1 [[2]] (.invertible ⟨1, [[2]]⟩ ⟨2, [[1, 0]]⟩)
#guard !checkInverseList 1 [[2, 0]] (.invertible ⟨1, [[2]]⟩ ⟨2, [[1]]⟩)

private def affine : SolveBasis where
  reduced := ⟨1, [[0, 1, 1]]⟩
  transform := ⟨1, [[1]]⟩
  inverse := ⟨1, [[1]]⟩
  rank := 1
  pivots := [1]
  free := [0, 2]
  value := ⟨1, [0, 2, 0]⟩
  nullity := 2
  basis := ⟨1, [[1, 0], [0, -1], [0, 1]]⟩

private def accepts (d : SolveBasis) : Bool :=
  checkSolveList 1 3 [[0, 1, 1]] [2] (.consistent ⟨1, [[0, 1, 1]]⟩ ⟨1, [2]⟩ d)

#guard accepts affine
#guard !accepts { affine with basis := ⟨1, [[1], [0], [0]]⟩ }
#guard !accepts { affine with basis := ⟨1, [[1, 1], [0, 0], [0, 0]]⟩ }
#guard !accepts { affine with basis := ⟨1, [[0, 0], [0, 0], [0, 0]]⟩ }
#guard !accepts { affine with nullity := 1, basis := ⟨1, [[1], [0], [0]]⟩ }
#guard !accepts { affine with free := [0, 0] }
#guard !accepts { affine with free := [2, 0] }
#guard !accepts { affine with free := [0, 1] }
#guard !accepts { affine with pivots := [0] }
#guard !accepts { affine with pivots := [3] }
#guard !accepts { affine with rank := 2 }
#guard !accepts { affine with reduced := ⟨1, [[1, 1, 1]]⟩ }
#guard !accepts { affine with reduced := ⟨1, [[0, 2, 1]]⟩ }
#guard !accepts { affine with transform := ⟨1, [[0]]⟩ }
#guard !accepts { affine with inverse := ⟨1, [[0]]⟩ }
#guard !accepts { affine with value := ⟨1, [0, 1, 0]⟩ }
#guard !accepts { affine with value := ⟨1, [3, 2, 0]⟩ }
#guard !accepts { affine with reduced := { affine.reduced with denom := 0 } }
#guard !accepts { affine with transform := { affine.transform with denom := 0 } }
#guard !accepts { affine with inverse := { affine.inverse with denom := 0 } }
#guard !accepts { affine with basis := { affine.basis with denom := 0 } }
#guard !accepts { affine with value := { affine.value with denom := 0 } }

#guard checkSolveList 1 1 [[0]] [1] (.inconsistent ⟨1, [[0]]⟩ ⟨1, [1]⟩ ⟨1, [1]⟩)
#guard !checkSolveList 1 1 [[1]] [1] (.inconsistent ⟨1, [[1]]⟩ ⟨1, [1]⟩ ⟨1, [1]⟩)
#guard !checkSolveList 1 1 [[0]] [1] (.inconsistent ⟨1, [[0]]⟩ ⟨1, [1]⟩ ⟨1, [0]⟩)
#guard !checkSolveList 1 1 [[0]] [1] (.inconsistent ⟨1, [[0]]⟩ ⟨0, [1]⟩ ⟨1, [1]⟩)
#guard !checkSolveList 1 1 [[0]] [1] (.inconsistent ⟨1, [[0]]⟩ ⟨1, [1]⟩ ⟨0, [1]⟩)
#guard !checkSolutionList 1 2 [[1, 2]] [5] [1]
#guard !checkSolutionList 1 2 [[1, 2]] [5] [1, 1]
#guard checkSolutionList 1 3 [[0, 1, 1]] [2] [3, 0, 2]

private def checkCase (c : RowReduceFixtures.Case Rat) : Bool := Id.run do
  unless checkSolveList c.n c.m (rowLists c.A) c.b.toList (solveWitness id c.A c.b) do
    return false
  if h : c.m = c.n then
    let A : Matrix Rat c.n c.n := h ▸ c.A
    unless checkInverseList c.n (rowLists A) (inverseWitness id A) do return false
  return true

#guard (RowReduceFixtures.cases (1 / 2 : Rat)).all checkCase

end Matrix.CertificateTests
