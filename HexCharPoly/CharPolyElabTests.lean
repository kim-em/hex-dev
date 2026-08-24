/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexCharPoly

namespace Hex.CharPolyElabTests

open Hex
open scoped Hex

def empty : Matrix Int 0 0 := Matrix.mk #v[]
def one : Matrix Int 1 1 := #m[7]
def dense : Matrix Int 2 2 := #m[1, 2; 3, 4]
def diagonal : Matrix Int 3 3 := #m[2, 0, 0; 0, -3, 0; 0, 0, 5]
def huge : Matrix Int 1 1 := #m[9223372036854775808]
def fromFn : Matrix Int 2 2 := Matrix.ofFn fun i j =>
  if i = j then (i.val : Int) + 1 else 0

#check char_poly #m[1, 2; 3, 4]

example : (char_poly empty).poly = #p[1] := rfl
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

end Hex.CharPolyElabTests
