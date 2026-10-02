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

example : ( !![1, 2, 3; 4, 5, 6; 7, 8, 9] : Matrix (Fin 3) (Fin 3) Int).charpoly =
    X ^ 3 - 15 * X ^ 2 - 18 * X := by char_poly

example : ( !![29, 106, -16, 45; -66, -41, 6, -106;
    123, -23, -125, 96; 11, 88, 97, -45] : Matrix (Fin 4) (Fin 4) Int).charpoly =
    X ^ 4 + 182 * X ^ 3 + 15099 * X ^ 2 + 1451563 * X + 112023617 := by char_poly

example : True := by
  char_poly dense
  have : dense.charpoly = poly := charPoly_eq
  exact True.intro

#check_failure char_poly (fun _ _ => (0 : Int) : Matrix Bool Bool Int)
#check_failure char_poly (!![1] : Matrix (Fin 1) (Fin 1) Nat)

end HexCharPolyMathlib.CharPolyElabTests

namespace HexCharPolyMathlib.CharPolyElabTests

theorem frontendAudit : dense.charpoly = Polynomial.X ^ 2 - 5 * Polynomial.X - 2 := by
  char_poly

noncomputable example : HexCharPolyMathlib.Certified dense := char_poly dense

/-- info: '_private.HexCharPolyMathlib.CharPolyElabTests.0.HexCharPolyMathlib.CharPolyElabTests.frontendAudit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms frontendAudit
/-- info: 'HexCharPolyMathlib.charpoly_eq_of_checkList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexCharPolyMathlib.charpoly_eq_of_checkList

/-- info: char_poly: the supplied polynomial has coefficients [0, 0, 1], but the computed characteristic polynomial has coefficients [-2, -5, 1] -/
#guard_msgs (whitespace := lax) in
#check_failure (char_poly : dense.charpoly = Polynomial.X ^ 2)

/-- info: char_poly declined: expected equal Mathlib row and column dimensions, but got Fin 1 and Fin 2 -/
#guard_msgs in
#check_failure char_poly ( !![1, 2] : Matrix (Fin 1) (Fin 2) Int)

end HexCharPolyMathlib.CharPolyElabTests
