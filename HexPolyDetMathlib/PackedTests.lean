/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib
import Mathlib.Algebra.Field.ZMod

set_option hex.det.checker 2
set_option trace.HexMatrix.certificate true

 theorem packedInteger (x y : Int) :
    Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
      (x ^ 2 - 1) * (y ^ 2 - 1) := by det

 theorem packedResidue (x y : ZMod 3) :
    Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
      (x ^ 2 - 1) * (y ^ 2 - 1) := by det

example (x y : Int) : Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
    (det% !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y]).value :=
  (det% !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y]).proof

example (x y : Int) : Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
    (x ^ 2 - 1) * (y ^ 2 - 1) := by
  simp only [Hex.normPolyDet]
  ring

example (x y : Rat) :
    Matrix.det !![x / 2, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
      (x ^ 2 / 2 - 1) * (y ^ 2 - 1) := by det

set_option hex.det.checker 3 in
example (x y : Int) : Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
    (x ^ 2 - 1) * (y ^ 2 - 1) := by det

set_option hex.det.quotients false in
example (x y : ZMod 3) : Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
    (x ^ 2 - 1) * (y ^ 2 - 1) := by det

/-- info: 'packedInteger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms packedInteger
/-- info: 'packedResidue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms packedResidue

/-- info: 'HexMatrixMathlib.DetPoly.Polynomial.checkDetPolyPacked_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexMatrixMathlib.DetPoly.Polynomial.checkDetPolyPacked_sound
/-- info: 'HexMatrixMathlib.DetPoly.Residue.checkDetPolyPackedMod_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexMatrixMathlib.DetPoly.Residue.checkDetPolyPackedMod_sound

set_option maxHeartbeats 0 in
example (x : Fin 17 → Int) : ∃ d : Int, Matrix.det !![x 0, x 1, x 2, x 3, 0; x 4, x 5, x 6, x 7, 0; x 8, x 9, x 10, x 11, 0; x 12, x 13, x 14, x 15, 0; 0, 0, 0, 0, x 16] = d := by
  exact ⟨_, (det% !![x 0, x 1, x 2, x 3, 0; x 4, x 5, x 6, x 7, 0; x 8, x 9, x 10, x 11, 0; x 12, x 13, x 14, x 15, 0; 0, 0, 0, 0, x 16]).proof⟩
