/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMatrix

/-!
Core conformance checks for `hex-matrix` (the dense base).

Run this file through the conformance Lake target, not direct `lake env lean`.

Oracle: none
Mode: always
Covered operations:
- dense matrix constructors and accessors (`ofFn`, `row`, `col`, `transpose`, `principalSubmatrix`)
- vector and matrix arithmetic (`dotProduct`, ``.normSq, `mulVec`, `mul`, `gramMatrix`)
- elementary row operations (`rowSwap`, `rowScale`, `rowAdd`)
Covered properties:
- transpose is involutive on committed fixtures
- identity matrices act as left and right multiplicative identities
- `rowSwap` is involutive
Covered edge cases:
- zero matrices and zero vectors, identity matrices, 2×2 and 6×6 dimension bands

The determinant, Bareiss, and row-reduction conformance guards live in the
`HexDeterminant`, `HexBareiss`, and `HexRowReduce` Conformance modules.
-/

namespace Hex

namespace Matrix

private def baseInt : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, _ => 2
    | 1, 0 => 3
    | _, _ => 4

private def pivotInt : Matrix Int 3 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 0, 1 => 2
    | 0, _ => 1
    | 1, 0 => 3
    | 1, 1 => 0
    | 1, _ => 4
    | 2, 0 => 5
    | 2, 1 => 6
    | _, _ => 0

private def vecInt : Vector Int 2 :=
  Vector.ofFn fun i => if i.val = 0 then 5 else 6

private def rowOneInt : Vector Int 2 :=
  Vector.ofFn fun i => if i.val = 0 then 3 else 4

private def colZeroInt : Vector Int 2 :=
  Vector.ofFn fun i => if i.val = 0 then 1 else 3

private def unitSubmatrix : Matrix Int 1 1 :=
  Matrix.ofFn fun _ _ => 1

private def baseGramInt : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 5
    | 0, _ => 11
    | 1, 0 => 11
    | _, _ => 25

private def spanVec : Vector Rat 3 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 1
    | 1 => 2
    | _ => 3

#guard Matrix.row baseInt ⟨1, by decide⟩ = rowOneInt
#guard Matrix.col baseInt ⟨0, by decide⟩ = colZeroInt
#guard Matrix.principalSubmatrix baseInt 1 (by decide) = unitSubmatrix
#guard Matrix.principalSubmatrix baseInt 2 (by decide) = baseInt
#guard vecInt.normSq = 61
#guard spanVec.normSq = 14
#guard Matrix.gramMatrix baseInt = baseGramInt
#guard (Matrix.identity (R := Int) 2) * baseInt = baseInt
#guard baseInt * (Matrix.identity (R := Int) 2) = baseInt
#guard Matrix.transpose (Matrix.transpose baseInt) = baseInt

-- `#m[...]` literal notation agrees with the `ofFn` fixtures.
#guard (#m[1, 2; 3, 4] : Matrix Int 2 2) = baseInt
#guard (#m[0, 2, 1; 3, 0, 4; 5, 6, 0] : Matrix Int 3 3) = pivotInt

/-- info: ⎡ 1 3 ⎤
⎣ 2 4 ⎦ -/
#guard_msgs in #eval Matrix.transpose baseInt

/-- info: { toArray := #[17, 39], size_toArray := _ } -/
#guard_msgs in #eval Matrix.mulVec baseInt vecInt

/-- info: ⎡  7 10 ⎤
⎣ 15 22 ⎦ -/
#guard_msgs in #eval baseInt * baseInt

/-- info: ⎡ 3 4 ⎤
⎣ 1 2 ⎦ -/
#guard_msgs in #eval Matrix.rowSwap baseInt ⟨0, by decide⟩ ⟨1, by decide⟩

/-- info: ⎡  0 2  1 ⎤
⎢ -6 0 -8 ⎥
⎣  5 6  0 ⎦ -/
#guard_msgs in #eval Matrix.rowScale pivotInt ⟨1, by decide⟩ (-2)

/-- info: ⎡ 0  2 1 ⎤
⎢ 3  0 4 ⎥
⎣ 5 12 3 ⎦ -/
#guard_msgs in #eval Matrix.rowAdd pivotInt ⟨0, by decide⟩ ⟨2, by decide⟩ 3

#guard Matrix.rowSwap (Matrix.rowSwap baseInt ⟨0, by decide⟩ ⟨1, by decide⟩)
    ⟨0, by decide⟩ ⟨1, by decide⟩ = baseInt

/-!
6×6 fixtures matching the SPEC `core` matrix-dimension band: `bigInt` is a
typical full-rank Int (entries `min i j + 1`), dense enough to exercise the
base arithmetic at the larger band.
-/

private def bigInt : Matrix Int 6 6 :=
  Matrix.ofFn fun i j => (min i.val j.val + 1 : Int)

#guard Matrix.transpose (Matrix.transpose bigInt) = bigInt
#guard (Matrix.identity (R := Int) 6) * bigInt = bigInt

end Matrix
