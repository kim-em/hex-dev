/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDeterminant
import HexDeterminant.Carriers

/-!
Core conformance checks for `hex-determinant`.

Run this file through the conformance Lake target, not direct `lake env lean`.

Oracle: `scripts/oracle/matrix_flint.py` (`det` op, via the
`hexdeterminant_emit_fixtures` stream)
Mode: always
Covered operations:
- the generic Leibniz determinant `det`
- the determinant behaviour of elementary row operations
Covered properties:
- `det` of the identity is `1`; `det` of zero / singular matrices is `0`
- row operations satisfy the determinant laws promised by the SPEC
  (`rowSwap` negates, `rowScale` scales, `rowAdd` preserves)
Covered edge cases:
- identity, zero, and singular matrices; a pivoting input with a zero leading entry
-/

namespace Hex

namespace Matrix

private def zeroInt : Matrix Int 2 2 := 0

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

#guard Matrix.det (Matrix.identity (R := Int) 2) = 1
#guard Matrix.det zeroInt = 0
#guard Matrix.det singularInt = 0
#guard Matrix.det (Matrix.rowSwap pivotInt ⟨0, by decide⟩ ⟨1, by decide⟩) = -Matrix.det pivotInt
#guard Matrix.det (Matrix.rowScale pivotInt ⟨1, by decide⟩ (-2)) = (-2) * Matrix.det pivotInt
#guard Matrix.det (Matrix.rowAdd pivotInt ⟨0, by decide⟩ ⟨2, by decide⟩ 3) = Matrix.det pivotInt

/- Determinant row-operation proof-mode automation examples. -/

example : Matrix.det (Matrix.identity (R := Int) 2) = 1 := by
  exact Matrix.det_identity

example (M : Matrix Int 3 3) (i j : Fin 3) (h : i ≠ j) :
    Matrix.det (Matrix.rowSwap M i j) = -Matrix.det M := by
  grind

example (M : Matrix Int 3 3) (i : Fin 3) (c : Int) :
    Matrix.det (Matrix.rowScale M i c) = c * Matrix.det M := by
  grind

example (M : Matrix Int 3 3) (src dst : Fin 3) (c : Int) (h : src ≠ dst) :
    Matrix.det (Matrix.rowAdd M src dst c) = Matrix.det M := by
  grind

end Matrix


namespace DeterminantCarriers
open scoped Hex.DeterminantCarriers

-- Direct instantiations also check the coefficient-ring and comparator inputs.
example (M : Matrix (DensePoly Int) n n) : DensePoly Int := Matrix.det M
example (M : Matrix (DensePoly Rat) n n) : DensePoly Rat := Matrix.det M
example (M : Matrix (DensePoly Mod) n n) : DensePoly Mod := Matrix.det M
example (M : Matrix (Sparse k Int) n n) : Sparse k Int := Matrix.det M
example (M : Matrix (Sparse k Rat) n n) : Sparse k Rat := Matrix.det M
example (M : Matrix (RationalFn Rat) n n) : RationalFn Rat := Matrix.det M

-- The diagonal products differ by one even though their high-degree terms cancel.
#guard Matrix.det (cancellation (intPoly 0 0 2)) = 1
#guard Matrix.det (cancellation (ratPoly 0 0 2)) = 1
#guard Matrix.det (cancellation (modPoly 0 0 2)) = 1
#guard (Matrix.det (cancellation (mixed 2 (2 : Int)))).termsList =
  (1 : Sparse 2 Int).termsList
#guard (Matrix.det (cancellation (mixed 3 (2/3 : Rat)))).termsList =
  (1 : Sparse 3 Rat).termsList
#guard Matrix.det (cancellation (fraction 0 0 2)) = 1
#guard (intMv 0 0 2).termsList.all (fun (m, _) => m.toList.all (· > 0))
#guard (ratMv 0 0 2).termsList.all (fun (m, _) => m.toList.all (· > 0))
#guard ((-102 : Mod).toNat, (204 : Mod).toNat) = (100, 2)

-- Every benchmark entry retains its declared nonunit denominator degree.
#guard ([1, 2, 4] : List Nat).all fun d =>
  (List.range 4).all fun r => (List.range 4).all fun c =>
    (fraction r c d).den.toArray.size == d + 1

end DeterminantCarriers
