/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexBareissMathlib
import Mathlib.Data.ZMod.Basic

/-! Build-only examples for the kernel determinant certificate and the `det`
tactic: a hand-written certificate discharged in the kernel, and the tactic in both orientations, on the four literal syntaxes, behind
definitions, on rational entries, on the empty matrix, on odd and even
dimensions with pivot swaps, on singular inputs, on a false target, on
symbolic entries (through `norm_det`), with `det` and `det%` leaving the
ordinary `det` identifiers untouched, and the axiom audit. -/

open Hex Hex.Matrix HexMatrixMathlib
open scoped Hex

/-! # The kernel certificate -/

/-- A `2 × 2` witness written by hand: no swaps, transform `[[1], [-3, 1]]`,
triangular product `[[1, 2], [0, -2]]`, value `-2`. -/
example : checkDetList 2 [[1, 2], [3, 4]] (.triangular [] [[1], [-3, 1]] (-2)) = true := by
  decide +kernel

example : Matrix.det (ofLists 2 2 [[1, 2], [3, 4]]) = -2 :=
  det_eq_of_checkList 2 _ (.triangular [] [[1], [-3, 1]] (-2)) (by decide +kernel)

/-- A singular `2 × 2` matrix, certified by the left kernel vector `(2, -1)`. -/
example : Matrix.det (ofLists 2 2 [[(1 : ℤ), 2], [2, 4]]) = 0 :=
  det_eq_of_checkList 2 _ (.singular [2, -1]) (by decide +kernel)

/-! # The `det` tactic -/

section DetTactic

/-- The `3 × 3` matrix as a Mathlib literal. -/
def detTestLit : Matrix (Fin 3) (Fin 3) ℤ := !![0, 2, 1; 3, 1, 4; 1, 5, 9]

-- both orientations, behind a definition
example : detTestLit.det = -32 := by det
example : -32 = detTestLit.det := by det
example : Matrix.det (R := ℤ) !![0, 2, 1; 3, 1, 4; 1, 5, 9] = -32 := by det

-- the four literal syntaxes
example : Matrix.det (R := ℤ) !![1, 2; 3, 4] = -2 := by det
example : Matrix.det (Matrix.of ![![(1 : ℤ), 2], ![3, 4]]) = -2 := by det
example : Matrix.det (fun i j : Fin 3 => if i = j then (2 : ℤ) else 1) = 4 := by det
example : Matrix.det (Matrix.ofArray (m := 2) (n := 2) #[(1 : ℤ), 2, 3, 4] rfl) = -2 := by det

/-- A `fun i j => …` literal behind a definition. -/
def detFromFn : Matrix (Fin 4) (Fin 4) ℤ := fun i j => (i.val : ℤ) ^ j.val

example : detFromFn.det = 12 := by det

-- compound entries, the empty matrix, and a `1 × 1` matrix
example : Matrix.det (R := ℤ) !![1 - 1, 2; 3, 2 * 2] = -6 := by det
example : Matrix.det (R := ℤ) !![] = 1 := by det
example : Matrix.det (R := ℤ) !![7] = 7 := by det

-- rational entries
example : Matrix.det (R := ℚ) !![1 / 2, -1; 3, 5 / 3] = 23 / 6 := by det
example : Matrix.det (R := ℚ) !![1, 2; 3, 4] = -2 := by det
example : Matrix.det (R := ℚ) !![1 / 3, 2 / 3; 1, 2] = 0 := by det

-- odd and even dimensions with pivot swaps
example : Matrix.det (R := ℤ) !![0, 0, 1; 0, 1, 0; 1, 0, 0] = -1 := by det
example : Matrix.det (R := ℤ) !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] = 1 := by det
example : Matrix.det (R := ℤ) !![0, 1, 2, 3, 4; 1, 0, 1, 2, 3; 0, 0, 0, 1, 1; 0, 0, 2, 0, 1; 0, 0, 0, 0, 3] =
    6 := by det

-- singular inputs
example : Matrix.det (R := ℤ) !![1, 2; 2, 4] = 0 := by det
example : Matrix.det (R := ℤ) !![0, 0; 0, 0] = 0 := by det
example : Matrix.det (R := ℤ) !![1, 2, 3; 4, 5, 6; 7, 8, 9] = 0 := by det
example : Matrix.det (R := ℤ) !![1, 2, 3; 2, 4, 6; 0, 0, 1] = 0 := by det

/-- A `16 × 16` matrix of `8`-bit entries. -/
def dense16 : Matrix (Fin 16) (Fin 16) ℤ :=
  !![-9, 2, 8, -1, -6, -2, -1, -8, 2, 1, 9, -6, 9, 8, -5, 0;
    2, 2, 9, -4, 4, -7, 7, 3, 6, 2, -2, -6, -5, -8, 0, 8;
    -1, 2, -6, 1, -5, -4, 8, 2, 3, -5, 8, 3, -8, -8, -7, 9;
    -6, 0, -6, 4, 8, -7, -2, 1, 4, 9, -9, 6, 3, -7, -5, -3;
    1, -7, 8, -2, -5, 3, 8, 5, 4, 7, -9, 3, 4, -3, -3, -3;
    -9, -7, -1, 4, -7, -2, 7, 5, 9, -7, 4, 1, 8, 1, 0, -7;
    -5, 2, -4, 4, 4, -1, -9, 3, 2, -7, -5, -2, -7, -8, 3, 4;
    5, -4, -1, -2, 4, 5, 1, 5, -7, -3, -6, 4, -9, -8, -5, 9;
    9, -7, -2, -7, -2, -1, 6, 2, -6, -9, 4, -6, 9, 9, 1, 7;
    2, 0, 4, 2, 5, 0, 8, 7, -7, -5, -4, -2, 1, -6, 4, -6;
    9, 6, 3, -2, 4, 2, 6, 9, -4, 4, -7, 6, 4, -1, 5, 8;
    2, 3, 6, -7, 4, 3, -7, 2, -3, 3, -9, 7, 0, -2, 2, 5;
    -8, 4, 1, -6, 5, -6, -6, -2, -9, 5, 5, 9, -9, -5, 0, 1;
    -5, 2, 8, -2, 0, -3, -8, -5, -1, -3, 2, 3, 3, -6, 6, -8;
    8, 5, 6, -4, -2, -5, 8, 0, -9, 3, -6, -8, 3, -8, 1, -5;
    3, -4, -2, -6, -9, 9, 6, -4, -3, -1, 8, -8, -4, 1, -8, 6]

theorem dense16_det : dense16.det = (det% dense16).value := (det% dense16).proof

-- the term form
example : (det% detTestLit).value = -32 := rfl
example : detTestLit.det = (det% detTestLit).value := (det% detTestLit).proof
example : (det% !![1, 2; 3, 4]).value = -2 := rfl
example : (det% (!![1 / 2, -1; 3, 5 / 3] : Matrix (Fin 2) (Fin 2) ℚ)).value = 23 / 6 := rfl

-- the simp set; symbolic entries and other carriers go through `norm_det`, which
-- normalizes the determinant as `eval_det` does and leaves the rest to `ring`
example : Matrix.det (R := ℤ) !![1, 2; 3, 4] = -2 := by simp only [hex_norm_det]
example : Matrix.det (R := ℚ) !![1 / 2, -1; 3, 5 / 3] = 23 / 6 := by simp only [hex_norm_det]
example (a b c d : ℤ) : Matrix.det !![a, b; c, d] = a * d - b * c := by
  simp only [hex_norm_det]
  ring
example (a b c d : ℤ) : Matrix.det !![a, b; c, d] = a * d - b * c := by
  det
  ring
example : Matrix.det (R := ZMod 7) !![1, 2; 3, 4] = 5 := by
  det
  decide

/-- error: det: the target is false: the determinant is -32 -/
#guard_msgs in
example : detTestLit.det = 5 := by det

/--
error: det: declined: the matrix is not a closed `!![…]`, `Matrix.of ![…]`, `fun i j => …` or `Matrix.ofArray` literal
  1 * 1
-/
#guard_msgs in
example : Matrix.det ((1 : Matrix (Fin 2) (Fin 2) ℤ) * 1) = 1 := by det

/-- A row of a `Matrix.of` chain that is not itself a vector chain. -/
def detRowFn : Fin 2 → ℤ := fun j => j.val + 3

/--
error: det: declined: the matrix is not a closed `!![…]`, `Matrix.of ![…]`, `fun i j => …` or `Matrix.ofArray` literal
  Matrix.of ![![1, 2], detRowFn]
-/
#guard_msgs in
example : Matrix.det (Matrix.of ![![(1 : ℤ), 2], detRowFn]) = -2 := by det

/-- A closed value that `norm_num` does not evaluate. -/
def detTarget : ℤ := -2

-- declined as a value, so the simp set rewrites the determinant and, as with
-- `eval_det`, leaves the rest of the goal
example : Matrix.det (R := ℤ) !![1, 2; 3, 4] = detTarget := by
  det
  rfl

/-- error: det: the goal is not `A.det = d` for a Mathlib matrix `A` -/
#guard_msgs in
example : (1 : ℤ) = 1 := by det

end DetTactic

/-! # `det` stays an ordinary identifier -/

example : Hex.Matrix.det (#m[1, 2; 3, 4] : Hex.Matrix Int 2 2) = -2 := by decide
example : det (#m[1, 2; 3, 4] : Hex.Matrix Int 2 2) = -2 := by decide

/-! # Axiom audit -/

theorem dense16_det' : dense16.det = -87982024952196733 := by det

/-- info: 'dense16_det'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dense16_det'
