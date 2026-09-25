/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs

namespace Determinant.Steps
variable {R : Type*} [CommRing R]

theorem iter_zero (n : Nat) (A : Array R) (i j : Nat) :
    ((BirdDet.stepEntry n A)^[0] (BirdDet.get n A)) i j = BirdDet.get n A i j := rfl

theorem iter_step (n : Nat) (A : Array R) (t i j : Nat) :
    ((BirdDet.stepEntry n A)^[t + 1] (BirdDet.get n A)) i j =
      -(BirdDet.sumFrom n (i + 1) fun k =>
        ((BirdDet.stepEntry n A)^[t] (BirdDet.get n A)) k k) * BirdDet.get n A i j +
      BirdDet.sumFrom n (i + 1) (fun k =>
        ((BirdDet.stepEntry n A)^[t] (BirdDet.get n A)) i k * BirdDet.get n A k j) := by
  rw [Function.iterate_succ_apply']
  rfl

end Determinant.Steps
