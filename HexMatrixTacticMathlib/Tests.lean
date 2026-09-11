/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexMatrixTacticMathlib

/-! Build-only regressions for the Mathlib frontends: the
characteristic-polynomial cases migrated from `HexCharPolyMathlib`, determinant
and rank goals on every literal syntax and in every orientation, the term
forms, the `hex_norm_det` simproc with its `norm_det` fallback, and the
syntax-compatibility checks. -/

namespace HexMatrixTacticMathlib.Tests

open Matrix Polynomial
open scoped Hex

def empty : Matrix (Fin 0) (Fin 0) Int := !![]
def dense : Matrix (Fin 2) (Fin 2) Int := !![1, 2; 3, 4]
def diagonal : Matrix (Fin 3) (Fin 3) Int := !![2, 0, 0; 0, -3, 0; 0, 0, 5]
def fromFn : Matrix (Fin 2) (Fin 2) Int := fun i j =>
  if i = j then (i.val : Int) + 1 else 0
def ofRows : Matrix (Fin 2) (Fin 2) Int := Matrix.of ![![1, 2], ![3, 4]]
def ofArr : Matrix (Fin 2) (Fin 2) Int := Matrix.ofArray #[1, 2, 3, 4] rfl
def swapped : Matrix (Fin 3) (Fin 3) Int := !![0, 1, 2; 3, 4, 5; 6, 7, 9]
def wide : Matrix (Fin 2) (Fin 3) Int := !![1, 2, 3; 2, 4, 6]
def zeroRows : Matrix (Fin 0) (Fin 3) Int := Matrix.of ![]
def zeroCols : Matrix (Fin 3) (Fin 0) Int := Matrix.of ![![], ![], ![]]
def zeroRowsNotation : Matrix (Fin 0) (Fin 3) Int := !![,,,]
def zeroColsNotation : Matrix (Fin 3) (Fin 0) Int := !![;;;]
def rational : Matrix (Fin 2) (Fin 2) ℚ := !![1/2, -1; 3, 5/3]
def rationalWide : Matrix (Fin 2) (Fin 3) ℚ := !![1/2, 1, 0; 1, 2, 0]

noncomputable def densePolynomial : Polynomial Int := X ^ 2 - 5 * X - 2

/-! # `char_poly` -/

#check char_poly !![1, 2; 3, 4]
#check char_poly (#m[1, 2; 3, 4] : Hex.Matrix Int 2 2)

example : (char_poly dense).poly = HexPolyMathlib.equiv #p[-2, -5, 1] := rfl
example : (char_poly dense).value = HexPolyMathlib.equiv #p[-2, -5, 1] := rfl
example : empty.charpoly = 1 := by char_poly
example : dense.charpoly = X ^ 2 - 5 * X - 2 := by char_poly
example : X ^ 2 - 5 * X - 2 = dense.charpoly := by char_poly
example : dense.charpoly = densePolynomial := by char_poly
example : diagonal.charpoly = X ^ 3 - 4 * X ^ 2 - 11 * X + 30 := by char_poly
example : fromFn.charpoly = X ^ 2 - 3 * X + 2 := by char_poly
example : ofArr.charpoly = X ^ 2 - 5 * X - 2 := by char_poly
example : dense.charpoly = X ^ 2 + C (-5) * X + C (-2) := by char_poly

example : True := by
  char_poly dense
  have : dense.charpoly = poly := charPoly_eq
  exact True.intro

#check_failure char_poly (fun _ _ => (0 : Int) : Matrix Bool Bool Int)
#check_failure char_poly (!![1] : Matrix (Fin 1) (Fin 1) Nat)

/-! # `det` -/

#check det% !![1, 2; 3, 4]

example : dense.det = -2 := by det
example : -2 = dense.det := by det
example : empty.det = 1 := by det
example : ofRows.det = -2 := by det
example : ofArr.det = -2 := by det
example : fromFn.det = 2 := by det
example : swapped.det = -3 := by det
example : rational.det = 23 / 6 := by det
example : Matrix.det !![1, 2; 3, 4] = -2 := by det

example : (det% dense).value = -2 := rfl
example : dense.det = (det% dense).value := (det% dense).proof
example : (det% rational).value = 23 / 6 := rfl

example : Matrix.det !![(1 : ℤ), 2; 3, 4] = -2 := by simp only [hex_norm_det]
example : Matrix.det rational = 23 / 6 := by simp only [hex_norm_det]
example {R : Type} [CommRing R] (a b c d : R) :
    Matrix.det !![a, b; c, d] = a * d - b * c := by
  simp only [hex_norm_det]
  ring

example : True := by
  fail_if_success (have : dense.det = 5 := by det)
  trivial

/-! # `rank` -/

#check rank% !![1, 2; 3, 4]

example : dense.rank = 2 := by rank
example : 2 = dense.rank := by rank
example : wide.rank = 1 := by rank
example : wide.rank ≤ 1 := by rank
example : wide.rank ≤ 3 := by rank
example : 1 ≤ wide.rank := by rank
example : wide.rank ≥ 1 := by rank
example : 1 ≥ wide.rank := by rank
example : empty.rank = 0 := by rank
example : zeroRows.rank = 0 := by rank
example : zeroCols.rank = 0 := by rank
example : zeroRowsNotation.rank = 0 := by rank
example : zeroColsNotation.rank = 0 := by rank
example : ofArr.rank = 2 := by rank
example : rational.rank = 2 := by rank
example : rationalWide.rank = 1 := by rank

example : (rank% wide).value = 1 := rfl
example : wide.rank = (rank% wide).value := (rank% wide).proof

example : True := by
  fail_if_success (have : wide.rank = 2 := by rank)
  fail_if_success (have : wide.rank ≤ 0 := by rank)
  fail_if_success (have : 2 ≤ wide.rank := by rank)
  trivial

/-! # Syntax compatibility: `det` and `rank` stay ordinary names. -/

example : det dense = -2 := by det
example : rank wide = 1 := by rank

open Hex.Matrix in
example : Hex.Matrix.det (#m[1, 2; 3, 4] : Hex.Matrix Int 2 2) = -2 := by det

open Hex.Matrix in
example : Hex.Matrix.rank (#m[1, 2; 3, 4] : Hex.Matrix Int 2 2) = 2 := by rank

end HexMatrixTacticMathlib.Tests
