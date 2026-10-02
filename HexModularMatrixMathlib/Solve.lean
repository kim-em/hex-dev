/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Complete
public import HexModularMatrix.Search
public import HexModularMatrixMathlib.Bound
public import HexMatrixMathlib.Vector
public import HexMatrixMathlib.Algebra
import all HexModularMatrix.Solve
import all HexModularMatrix.Decomp
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace HexModularMatrixMathlib

open HexMatrixMathlib

variable {A : Hex.Matrix Int n n} {b y : Vector Int n} {fuel : Nat} {d : Int}

/-- The checked integer solution is a rational solution of Mathlib's system. -/
theorem solve_eq (h : Hex.Matrix.solve? A b fuel = some (y, d)) :
    Matrix.mulVec ((matrixEquiv A).map (Int.cast : ℤ → ℚ))
      (fun i => ((y[i] : ℤ) : ℚ) / d) = fun i => ((b[i] : ℤ) : ℚ) := by
  obtain ⟨he, hd⟩ := Hex.Matrix.solve?_spec h
  have hq : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hm := (vectorEquiv_mulVec A y).symm.trans (congrArg vectorEquiv he)
  funext i
  have hi := congrFun hm i
  simp only [Matrix.mulVec, dotProduct, vectorEquiv_apply, Fin.getElem_fin,
    Vector.getElem_smul, smul_eq_mul] at hi
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, ← mul_div_assoc,
    ← Finset.sum_div]
  apply (div_eq_iff hq).mpr
  have hc : (∑ j, ((matrixEquiv A i j : ℤ) : ℚ) * ((y[j] : ℤ) : ℚ)) =
      (d : ℚ) * ((b[i] : ℤ) : ℚ) := by exact_mod_cast hi
  simpa only [mul_comm] using hc

/-- A returned witness certifies nonsingularity in Mathlib. -/
theorem solveWitness_det_ne_zero {w : Hex.Matrix.SolveWitness n}
    (h : Hex.Matrix.solveWitness? A b fuel = some w) : (matrixEquiv A).det ≠ 0 := by
  rw [← HexMatrixMathlib.det_eq A]
  exact Hex.Matrix.solveWitness?_det_ne_zero h

/-- A returned witness gives both the rational equation and nonsingularity. -/
theorem solveWitness_eq {w : Hex.Matrix.SolveWitness n}
    (h : Hex.Matrix.solveWitness? A b fuel = some w) :
    Matrix.mulVec ((matrixEquiv A).map (Int.cast : ℤ → ℚ))
      (fun i => ((w.num[i] : ℤ) : ℚ) / w.den) = (fun i => ((b[i] : ℤ) : ℚ)) ∧
      (matrixEquiv A).det ≠ 0 :=
  ⟨solve_eq (Hex.Matrix.solveWitness?_solve h), solveWitness_det_ne_zero h⟩

/-- The checked solution agrees with the nonsingular inverse. -/
theorem solve_eq_inv (h : Hex.Matrix.solve? A b fuel = some (y, d)) :
    (fun i => ((y[i] : ℤ) : ℚ) / d) =
      ((matrixEquiv A).map (Int.cast : ℤ → ℚ))⁻¹.mulVec (fun i => ((b[i] : ℤ) : ℚ)) := by
  have hi : (matrixEquiv A).det ≠ 0 := by
    rw [← HexMatrixMathlib.det_eq A]
    exact Hex.Matrix.solve?_det_ne_zero h
  have hq : IsUnit (((matrixEquiv A).map (Int.cast : ℤ → ℚ)).det) := by
    rw [← Int.cast_det, isUnit_iff_ne_zero]
    exact_mod_cast hi
  rw [← solve_eq h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hq, Matrix.one_mulVec]

/-- All columns share the reconstructed denominator. -/
theorem solveMat_eq {C X : Hex.Matrix Int n m}
    (h : Hex.Matrix.solveMat? A C fuel = some (X, d)) :
    (matrixEquiv A).map (Int.cast : ℤ → ℚ) * (matrixEquiv X).map (fun x => (x : ℚ) / d) =
      (matrixEquiv C).map (Int.cast : ℤ → ℚ) := by
  obtain ⟨he, hd⟩ := Hex.Matrix.solveMat?_spec h
  have hq : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hm := congrArg matrixEquiv he
  rw [matrixEquiv_mul, matrixEquiv_smul] at hm
  ext i j
  have hi := congrFun (congrFun hm i) j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at hi
  simp only [Matrix.mul_apply, Matrix.map_apply, ← mul_div_assoc, ← Finset.sum_div]
  apply (div_eq_iff hq).mpr
  have hc : (∑ k, ((matrixEquiv A i k : ℤ) : ℚ) * ((matrixEquiv X k j : ℤ) : ℚ)) =
      (d : ℚ) * ((matrixEquiv C i j : ℤ) : ℚ) := by exact_mod_cast hi
  simpa only [mul_comm] using hc

/-- The default search budget suffices while the supplied primes exceed `2^30`. -/
theorem solve_isSome_of_det_ne_zero (hA : (matrixEquiv A).det ≠ 0)
    (hsupply : ∀ q ∈ Hex.ZMod64.primesBelow (2 ^ 31 - 1) (Hex.Matrix.solveFuel A),
      2 ^ 30 < q.m) : (Hex.Matrix.solve? A b (Hex.Matrix.solveFuel A)).isSome := by
  have hd := Hex.Matrix.decomp?_isSome (A := A) (by intro hz; exact hA ((HexMatrixMathlib.det_eq A).symm.trans hz))
    (fuel := Hex.Matrix.solveFuel A) (by simp [Hex.Matrix.solveFuel]) hsupply
  cases h : Hex.Matrix.decomp? A (Hex.Matrix.solveFuel A) with
  | none => simp [h] at hd
  | some D =>
    simpa only [Hex.Matrix.solve?, h, Option.bind_some] using Hex.Matrix.solveWith_isSome D b

end HexModularMatrixMathlib
