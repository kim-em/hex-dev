/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexMatrixTactic

/-! Build-only regressions for the Hex frontends: the characteristic-polynomial
cases migrated from `HexCharPoly`, determinant goals in every supported
orientation, the term forms, and the syntax-compatibility checks (`det`
remains an ordinary identifier and function application). -/

namespace Hex.MatrixTacticTests

open Hex
open scoped Hex

def empty : Matrix Int 0 0 := Matrix.mk #v[]
def one : Matrix Int 1 1 := #m[7]
def dense : Matrix Int 2 2 := #m[1, 2; 3, 4]
def diagonal : Matrix Int 3 3 := #m[2, 0, 0; 0, -3, 0; 0, 0, 5]
def huge : Matrix Int 1 1 := #m[9223372036854775808]
def fromFn : Matrix Int 2 2 := Matrix.ofFn fun i j =>
  if i = j then (i.val : Int) + 1 else 0
def swapped : Matrix Int 3 3 := #m[0, 1, 2; 3, 4, 5; 6, 7, 9]
def dense4 : Matrix Int 4 4 := #m[2, -1, 0, 4; 3, 5, 7, -2; -4, 1, 9, 3; 1, 1, 1, 1]
def singular : Matrix Int 3 3 := #m[1, 2, 3; 2, 4, 6; 1, 0, 1]
def lateFail : Matrix Int 3 3 := #m[1, 0, 0; 0, 1, 0; 0, 0, 0]
def rational2 : Matrix Rat 2 2 := #m[1/2, -1; 3, 5/3]

/-! # `char_poly` -/

#check char_poly #m[1, 2; 3, 4]

example : (char_poly empty).poly = #p[1] := rfl
example : (char_poly dense).value = #p[-2, -5, 1] := rfl
example : Matrix.charPoly empty = #p[1] := by char_poly
example : Matrix.charPoly one = #p[-7, 1] := by char_poly
example : Matrix.charPoly dense = #p[-2, -5, 1] := by char_poly
example : #p[-2, -5, 1] = Matrix.charPoly dense := by char_poly
example : Matrix.charPoly diagonal = #p[30, -11, -4, 1] := by char_poly
example : Matrix.charPoly huge = #p[-9223372036854775808, 1] := by char_poly
example : Matrix.charPoly fromFn = #p[2, -3, 1] := by char_poly

example : True := by
  char_poly dense
  have : Matrix.charPoly dense = poly := charPoly_eq
  exact True.intro

#check_failure char_poly (#m[1] : Matrix Nat 1 1)
#check_failure char_poly (#m[1, 2] : Matrix Int 1 2)

/-! # `det` -/

#check det% #m[1, 2; 3, 4]

example : Matrix.bareiss dense = -2 := by det
example : -2 = Matrix.bareiss dense := by det
example : Matrix.bareiss empty = 1 := by det
example : Matrix.bareiss one = 7 := by det
example : Matrix.bareiss swapped = -3 := by det
example : Matrix.bareiss dense4 = 189 := by det
example : Matrix.bareiss singular = 0 := by det
example : Matrix.bareiss lateFail = 0 := by det
example : Matrix.bareissWith HexArith.Int.exactDiv dense4 = 189 := by det
example : Matrix.det dense = -2 := by det
example : Matrix.det swapped = -3 := by det
example : Matrix.det dense4 = 189 := by det
example : Matrix.det empty = 1 := by det

example : (det% dense).value = -2 := rfl
example : Matrix.bareiss dense = (det% dense).value := (det% dense).proof
example : (det% dense4).value = 189 := rfl

example : True := by
  fail_if_success (have : Matrix.bareiss dense = 5 := by det)
  fail_if_success (have : Matrix.det dense = 5 := by det)
  trivial

/-! # Syntax compatibility: `det` stays an ordinary name. -/

open Hex.Matrix in
example : det dense = -2 := by det

def det : Nat := 3

example : det = 3 := rfl
example (x : Nat) : x % 2 = x % 2 := rfl

end Hex.MatrixTacticTests
