/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexCharPolyMathlib

namespace HexCharPolyMathlib.CharPolyElabTests

open Matrix Polynomial
open scoped Hex

def empty : Matrix (Fin 0) (Fin 0) Int := !![]
def dense : Matrix (Fin 2) (Fin 2) Int := !![1, 2; 3, 4]
def diagonal : Matrix (Fin 3) (Fin 3) Int := !![2, 0, 0; 0, -3, 0; 0, 0, 5]
def fromFn : Matrix (Fin 2) (Fin 2) Int := fun i j =>
  if i = j then (i.val : Int) + 1 else 0

noncomputable def densePolynomial : Polynomial Int := X ^ 2 - 5 * X - 2

#check char_poly !![1, 2; 3, 4]
#check char_poly (#m[1, 2; 3, 4] : Hex.Matrix Int 2 2)

example : (char_poly dense).poly = HexPolyMathlib.equiv #p[-2, -5, 1] := rfl
example : empty.charpoly = 1 := by char_poly
example : dense.charpoly = X ^ 2 - 5 * X - 2 := by char_poly
example : X ^ 2 - 5 * X - 2 = dense.charpoly := by char_poly
example : dense.charpoly = densePolynomial := by char_poly
example : diagonal.charpoly = X ^ 3 - 4 * X ^ 2 - 11 * X + 30 := by char_poly
example : fromFn.charpoly = X ^ 2 - 3 * X + 2 := by char_poly
example : dense.charpoly = X ^ 2 + C (-5) * X + C (-2) := by char_poly

example : True := by
  char_poly dense
  have : dense.charpoly = poly := charPoly_eq
  exact True.intro

#check_failure char_poly (fun _ _ => (0 : Int) : Matrix Bool Bool Int)
#check_failure char_poly (!![1] : Matrix (Fin 1) (Fin 1) Nat)

end HexCharPolyMathlib.CharPolyElabTests
