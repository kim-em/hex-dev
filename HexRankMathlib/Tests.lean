/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexRank
import HexRankMathlib
import HexMatrix.Notation

/-! Build-only examples: a hand-written certificate discharged in the kernel,
the integer producer, the `Decidable` instance, and the scalar-extension
theorem at the two fraction-field instances a consumer meets. -/

open Hex Hex.Matrix HexMatrixMathlib
open scoped Hex

/-- A `3 × 4` integer matrix of rank `2`. -/
def rankTestMatrix : Hex.Matrix Int 3 4 := #m[1, 2, 3, 4; 2, 4, 6, 8; 1, 0, 1, 0]

/-- A hand-written certificate for it. -/
def rankTestCert : RankCert Int 3 4 :=
  ⟨2, #v[0, 2], #v[0, 1], -2, #m[0, -2; -1, 1]⟩

example : (matrixEquiv rankTestMatrix).rank = 2 :=
  checkRank_sound (A := rankTestMatrix) (c := rankTestCert) (by decide +kernel)

example : (matrixEquiv rankTestMatrix).rank = 2 :=
  (rank_eq_rank rankTestMatrix).symm.trans (by decide +kernel)

example : (matrixEquiv rankTestMatrix).rank = 2 := by decide +kernel

example (M : Matrix (Fin 3) (Fin 4) ℤ) : (M.map (algebraMap ℤ ℚ)).rank = M.rank :=
  rank_map_eq M

example (M : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    (M.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).rank = M.rank :=
  rank_map_eq M

example [CommRing R] [IsDomain R] [DecidableEq R] (A : Hex.Matrix R 2 2) :
    ∃ c : RankCert R 2 2, checkRank A c = true :=
  exists_rankCert A


/-! # The `rank` tactic -/

section RankTactic

/-- The `3 × 4` matrix of rank `2` as a Mathlib literal. -/
def rankTestLit : Matrix (Fin 3) (Fin 4) ℤ := !![1, 2, 3, 4; 2, 4, 6, 8; 1, 0, 1, 0]

example : rankTestLit.rank = 2 := by rank
example : 2 = rankTestLit.rank := by rank
example : rankTestLit.rank ≤ 2 := by rank
example : rankTestLit.rank ≤ 3 := by rank
example : 2 ≤ rankTestLit.rank := by rank
example : rankTestLit.rank ≥ 1 := by rank
example : 3 ≥ rankTestLit.rank := by rank
example : Matrix.rank (R := ℤ) !![1 - 1, 2; 3, 4] = 2 := by rank
example : Matrix.rank (Matrix.of ![![(1 : ℤ), 0], ![0, 1]]) = 2 := by rank
example : Matrix.rank (R := ℤ) !![] = 0 := by rank
example : Matrix.rank (R := ℤ) !![,,,] = 0 := by rank
example : Matrix.rank (R := ℤ) !![;;;] = 0 := by rank
example : Matrix.rank (R := ℤ) !![0, 0; 0, 0] = 0 := by rank
example : Matrix.rank (R := ℤ) !![1, 2, 3; 2, 4, 6] = 1 := by rank
example : Matrix.rank (R := ℤ) !![1; 2; 3] = 1 := by rank
example : Matrix.rank (R := ℤ) !![0, 1; 0, 0] = 1 := by rank

/-- A `16 × 16` matrix of full rank. -/
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

example : dense16.rank = 16 := by rank

/-- A `32 × 32` matrix of rank `2`. -/
def lowRank32 : Matrix (Fin 32) (Fin 32) ℤ :=
  !![5, 0, 1, -1, 1, 5, 0, 0, 6, -3, 0, -2, 0, -2, 3, -2, -1, 1, -2, 4, 3, -3, 0, 4, 2, 3, 0, -3, -4, -3, 4, -2;
    -1, -9, -2, -4, -5, -4, -6, -3, -3, 0, 6, 4, -6, 7, -6, 7, -4, 1, 4, 1, -3, 0, -3, -5, -4, -6, 9, -3, -1, -3, -5, -2;
    4, 6, 2, 2, 4, 6, 4, 2, 6, -2, -4, -4, 4, -6, 6, -6, 2, 0, -4, 2, 4, -2, 2, 6, 4, 6, -6, 0, -2, 0, 6, 0;
    10, 0, 2, -2, 2, 10, 0, 0, 12, -6, 0, -4, 0, -4, 6, -4, -2, 2, -4, 8, 6, -6, 0, 8, 4, 6, 0, -6, -8, -6, 8, -4;
    10, 0, 2, -2, 2, 10, 0, 0, 12, -6, 0, -4, 0, -4, 6, -4, -2, 2, -4, 8, 6, -6, 0, 8, 4, 6, 0, -6, -8, -6, 8, -4;
    7, 3, 2, 0, 3, 8, 2, 1, 9, -4, -2, -4, 2, -5, 6, -5, 0, 1, -4, 5, 5, -4, 1, 7, 4, 6, -3, -3, -5, -3, 7, -2;
    4, -9, -1, -5, -4, 1, -6, -3, 3, -3, 6, 2, -6, 5, -3, 5, -5, 2, 2, 5, 0, -3, -3, -1, -2, -3, 9, -6, -5, -6, -1, -4;
    11, -6, 1, -5, -1, 9, -4, -2, 12, -7, 4, -2, -4, 0, 3, 0, -5, 3, -2, 10, 5, -7, -2, 6, 2, 3, 6, -9, -10, -9, 6, -6;
    3, -3, 0, -2, -1, 2, -2, -1, 3, -2, 2, 0, -2, 1, 0, 1, -2, 1, 0, 3, 1, -2, -1, 1, 0, 0, 3, -3, -3, -3, 1, -2;
    1, 9, 2, 4, 5, 4, 6, 3, 3, 0, -6, -4, 6, -7, 6, -7, 4, -1, -4, -1, 3, 0, 3, 5, 4, 6, -9, 3, 1, 3, 5, 2;
    4, -9, -1, -5, -4, 1, -6, -3, 3, -3, 6, 2, -6, 5, -3, 5, -5, 2, 2, 5, 0, -3, -3, -1, -2, -3, 9, -6, -5, -6, -1, -4;
    -13, 3, -2, 4, -1, -12, 2, 1, -15, 8, -2, 4, 2, 3, -6, 3, 4, -3, 4, -11, -7, 8, 1, -9, -4, -6, -3, 9, 11, 9, -9, 6;
    0, 15, 3, 7, 8, 5, 10, 5, 3, 1, -10, -6, 10, -11, 9, -11, 7, -2, -6, -3, 4, 1, 5, 7, 6, 9, -15, 6, 3, 6, 7, 4;
    9, -9, 0, -6, -3, 6, -6, -3, 9, -6, 6, 0, -6, 3, 0, 3, -6, 3, 0, 9, 3, -6, -3, 3, 0, 0, 9, -9, -9, -9, 3, -6;
    15, 0, 3, -3, 3, 15, 0, 0, 18, -9, 0, -6, 0, -6, 9, -6, -3, 3, -6, 12, 9, -9, 0, 12, 6, 9, 0, -9, -12, -9, 12, -6;
    -9, 9, 0, 6, 3, -6, 6, 3, -9, 6, -6, 0, 6, -3, 0, -3, 6, -3, 0, -9, -3, 6, 3, -3, 0, 0, -9, 9, 9, 9, -3, 6;
    -5, 15, 2, 8, 7, 0, 10, 5, -3, 4, -10, -4, 10, -9, 6, -9, 8, -3, -4, -7, 1, 4, 5, 3, 4, 6, -15, 9, 7, 9, 3, 6;
    3, -3, 0, -2, -1, 2, -2, -1, 3, -2, 2, 0, -2, 1, 0, 1, -2, 1, 0, 3, 1, -2, -1, 1, 0, 0, 3, -3, -3, -3, 1, -2;
    9, 6, 3, 1, 5, 11, 4, 2, 12, -5, -4, -6, 4, -8, 9, -8, 1, 1, -6, 6, 7, -5, 2, 10, 6, 9, -6, -3, -6, -3, 10, -2;
    13, -3, 2, -4, 1, 12, -2, -1, 15, -8, 2, -4, -2, -3, 6, -3, -4, 3, -4, 11, 7, -8, -1, 9, 4, 6, 3, -9, -11, -9, 9, -6;
    12, 3, 3, -1, 4, 13, 2, 1, 15, -7, -2, -6, 2, -7, 9, -7, -1, 2, -6, 9, 8, -7, 1, 11, 6, 9, -3, -6, -9, -6, 11, -4;
    -11, 6, -1, 5, 1, -9, 4, 2, -12, 7, -4, 2, 4, 0, -3, 0, 5, -3, 2, -10, -5, 7, 2, -6, -2, -3, -6, 9, 10, 9, -6, 6;
    4, -9, -1, -5, -4, 1, -6, -3, 3, -3, 6, 2, -6, 5, -3, 5, -5, 2, 2, 5, 0, -3, -3, -1, -2, -3, 9, -6, -5, -6, -1, -4;
    9, 6, 3, 1, 5, 11, 4, 2, 12, -5, -4, -6, 4, -8, 9, -8, 1, 1, -6, 6, 7, -5, 2, 10, 6, 9, -6, -3, -6, -3, 10, -2;
    -11, 6, -1, 5, 1, -9, 4, 2, -12, 7, -4, 2, 4, 0, -3, 0, 5, -3, 2, -10, -5, 7, 2, -6, -2, -3, -6, 9, 10, 9, -6, 6;
    4, 6, 2, 2, 4, 6, 4, 2, 6, -2, -4, -4, 4, -6, 6, -6, 2, 0, -4, 2, 4, -2, 2, 6, 4, 6, -6, 0, -2, 0, 6, 0;
    1, -6, -1, -3, -3, -1, -4, -2, 0, -1, 4, 2, -4, 4, -3, 4, -3, 1, 2, 2, -1, -1, -2, -2, -2, -3, 6, -3, -2, -3, -2, -2;
    -15, 0, -3, 3, -3, -15, 0, 0, -18, 9, 0, 6, 0, 6, -9, 6, 3, -3, 6, -12, -9, 9, 0, -12, -6, -9, 0, 9, 12, 9, -12, 6;
    5, -15, -2, -8, -7, 0, -10, -5, 3, -4, 10, 4, -10, 9, -6, 9, -8, 3, 4, 7, -1, -4, -5, -3, -4, -6, 15, -9, -7, -9, -3, -6;
    0, 15, 3, 7, 8, 5, 10, 5, 3, 1, -10, -6, 10, -11, 9, -11, 7, -2, -6, -3, 4, 1, 5, 7, 6, 9, -15, 6, 3, 6, 7, 4;
    -8, 3, -1, 3, 0, -7, 2, 1, -9, 5, -2, 2, 2, 1, -3, 1, 3, -2, 2, -7, -4, 5, 1, -5, -2, -3, -3, 6, 7, 6, -5, 4;
    1, -6, -1, -3, -3, -1, -4, -2, 0, -1, 4, 2, -4, 4, -3, 4, -3, 1, 2, 2, -1, -1, -2, -2, -2, -3, 6, -3, -2, -3, -2, -2]

example : lowRank32.rank = 2 := by rank
example : lowRank32.rank ≤ 2 := by rank

/-- error: rank: the target is false: the rank is 2 -/
#guard_msgs in
example : Matrix.rank (R := ℤ) !![1, 2; 3, 4] = 1 := by rank

/--
error: rank: declined: the matrix
  !![a, 1; 1, a]
must be a closed term
-/
#guard_msgs in
example (a : ℤ) : Matrix.rank !![a, 1; 1, a] = 2 := by rank

/--
error: rank: declined: only integer matrices are supported; the entry type is
  ℚ
-/
#guard_msgs in
example : Matrix.rank (R := ℚ) !![1 / 2, 1; 1, 2] = 1 := by rank

/--
error: rank: declined: the matrix is not a closed `!![…]` or `Matrix.of ![…]` literal
  1 * 1
-/
#guard_msgs in
example : Matrix.rank ((1 : Matrix (Fin 2) (Fin 2) ℤ) * 1) = 2 := by rank

end RankTactic
