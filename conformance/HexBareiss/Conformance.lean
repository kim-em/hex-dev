/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBareiss

/-!
Core conformance checks for `hex-bareiss`.

Run this file through the conformance Lake target (not direct `lake env lean`):
the Bareiss guards need the native code generated for `Matrix.exactDiv`.

Oracle: `scripts/oracle/matrix_flint.py` (`bareiss` op, via the
`hexbareiss_emit_fixtures` stream)
Mode: always
Covered operations:
- the executable fraction-free Bareiss determinant `bareiss` and `bareissData`
Covered properties:
- committed Bareiss fixtures match their expected executable determinant values;
  the `bareiss = det` guards below are value-level fixture checks only, not a
  general theorem in the Mathlib-free layer
- `bareissData` records the determinant and the row-swap count
Covered edge cases:
- zero, singular, and pivoting (zero leading entry) inputs at the 2×2/3×3/6×6 bands
- determinant behaviour under elementary row operations on a 6×6 fixture
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

private def singularInt : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, _ => 2
    | 1, 0 => 2
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

/- Bareiss fixture equality guards.

These evaluate committed examples against `Matrix.det` to catch runtime
regressions on representative nonsingular, singular, and pivoting inputs. They
do not expose or imply a general Mathlib-free bridge theorem of the forbidden
shape `Matrix.bareiss M = Matrix.det M`. -/

#guard Matrix.bareiss baseInt = Matrix.det baseInt
#guard Matrix.bareiss singularInt = 0
#guard Matrix.bareiss pivotInt = Matrix.det pivotInt
#guard (Matrix.bareissData singularInt).det = 0
#guard (Matrix.bareissData pivotInt).rowSwaps = 1

/-!
6×6 fixtures matching the SPEC `core` matrix-dimension band:

- `bigInt` — typical full-rank Int (entries `min i j + 1`); `det = 1`.
- `bigZeroInt` — edge zero matrix.
- `bigSingularInt` — adversarial singular Int with row 1 proportional to row 0.
- `bigPivotInt` — adversarial zero leading pivot (`M[0][0] = 0`), forcing one
  Bareiss row swap.
-/

private def bigInt : Matrix Int 6 6 :=
  Matrix.ofFn fun i j => (min i.val j.val + 1 : Int)

private def bigZeroInt : Matrix Int 6 6 := 0

private def bigSingularInt : Matrix Int 6 6 :=
  Matrix.ofFn fun i j =>
    if i.val = 1 then (2 : Int)
    else (min i.val j.val + 1 : Int)

private def bigPivotInt : Matrix Int 6 6 :=
  Matrix.ofFn fun i j =>
    if i.val = 0 ∧ j.val = 0 then (0 : Int)
    else (min i.val j.val + 1 : Int)

/- Bareiss executable-value guards for 6×6 fixtures.

These compare against known fixture values rather than stating any general
relationship between the Bareiss algorithm and Leibniz determinant. -/

#guard Matrix.bareiss bigInt = 1
#guard Matrix.bareiss bigZeroInt = 0
#guard Matrix.bareiss bigSingularInt = 0
#guard Matrix.bareiss bigPivotInt = -1
#guard (Matrix.bareissData bigPivotInt).rowSwaps = 1

#guard Matrix.bareiss (Matrix.rowSwap bigInt ⟨0, by decide⟩ ⟨5, by decide⟩) = -1
#guard Matrix.bareiss (Matrix.rowScale bigInt ⟨2, by decide⟩ 4) = 4
#guard Matrix.bareiss (Matrix.rowAdd bigInt ⟨0, by decide⟩ ⟨3, by decide⟩ 7) = 1

end Matrix
