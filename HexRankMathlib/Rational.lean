/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRankMathlib.Kernel
public import HexRankMathlib.Extension
public import HexBareissMathlib.Kernel

public section

/-! Rank certificates for rational rows, using the integer checker after
clearing each row's denominators. -/

namespace HexMatrixMathlib

open Hex.Matrix

/-- Positive row scales identify a rational matrix with an integer matrix
without changing its rank. Both checks recurse only over literal lists. -/
theorem rank_eq_of_scaledRows {n m : Nat} (A : Matrix (Fin n) (Fin m) ℚ)
    (L : List (List Rat)) (s : List Nat) (B : List (List Int)) (c : RankWitness)
    (hA : A = ofLists n m L) (hs : DetWitness.scaledRows s L B = true)
    (hc : checkRankList n m B c = true) : A.rank = c.rank := by
  classical
  subst A
  have hrows := scaledRows_spec s L B hs
  let D : Matrix (Fin n) (Fin n) ℚ := Matrix.diagonal fun i => (s.getD i 1 : ℚ)
  have hDA : D * ofLists n m L = (ofLists n m B).map (algebraMap ℤ ℚ) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.map_apply, ofLists_apply, ofLists_apply]
    exact (hrows i).2 j
  have hD : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (hrows i).1.ne'
  calc
    (ofLists n m L).rank = (D * ofLists n m L).rank :=
      (Matrix.rank_mul_eq_right_of_det_ne_zero D _ hD).symm
    _ = ((ofLists n m B).map (algebraMap ℤ ℚ)).rank := congrArg Matrix.rank hDA
    _ = (ofLists n m B).rank := rank_map_eq _
    _ = c.rank := rank_eq_of_checkList n m B c hc

end HexMatrixMathlib
