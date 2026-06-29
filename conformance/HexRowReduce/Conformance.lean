/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRowReduce

/-!
Core conformance checks for `hex-row-reduce`.

Run this file through the conformance Lake target, not direct `lake env lean`.

Oracle: `scripts/oracle/matrix_flint.py` (`rank` / `rowReduce` / `nullspace` ops,
via the `hexrowreduce_emit_fixtures` stream)
Mode: always
Covered operations:
- row reduction and span APIs (`rowReduce`, `rowReduce_rank`, `spanCoeffs`,
  `rowCombination`, `spanContains`)
- nullspace basis extraction (`nullspace`, `nullspaceBasisMatrix`)
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
#guard let D := Matrix.rowReduce fullRat22; D.echelon = (1 : Matrix Rat 2 2)

#guard Matrix.spanCoeffs dependentRat spanVec = some spanCoeffsWitness
#guard Matrix.rowCombination dependentRat spanCoeffsWitness = spanVec
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
    Matrix.spanCoeffs M v = some c → Matrix.rowCombination M c = v := by
  exact Matrix.spanCoeffs_sound M v c

example (M : Matrix Rat n m) (v : Vector Rat m) :
    Matrix.spanContains M v = (Matrix.spanCoeffs M v).isSome := by
  simp

example (M : Matrix Rat n m) (v : Vector Rat m) :
    Matrix.spanContains M v = true →
      ∃ c : Vector Rat n, Matrix.rowCombination M c = v := by
  exact (Matrix.spanContains_iff M v).mp

example (M : Matrix Rat n m) (k : Fin (m - Matrix.rowReduce_rank M)) :
    M * (Matrix.nullspace M).get k = 0 := by
  grind

example (M : Matrix Rat n m) (k : Fin (m - Matrix.rowReduce_rank M)) :
    Matrix.col (Matrix.nullspaceBasisMatrix M) k = (Matrix.nullspace M).get k := by
  grind

end RowReduceWrapperAutomation

end Matrix
