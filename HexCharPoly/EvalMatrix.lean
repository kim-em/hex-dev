/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexCharPoly.Trace

public section

/-!
Horner evaluation of a dense polynomial at a square matrix.
-/

namespace Hex.Matrix

universe u

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R] {n : Nat}

/-- Horner evaluation of a dense polynomial at a square matrix.  A scalar
coefficient acts by scaling the identity matrix. -/
@[expose]
noncomputable def evalMatrix (p : DensePoly R) (A : Matrix R n n) : Matrix R n n :=
  DensePoly.evalCoeffList (p.toList.map fun c => c • Matrix.identity n) A

/-- Compiled Horner loop for `evalMatrix`, using the cache-friendly matrix
multiplication kernel directly. -/
@[expose]
def evalMatrixImpl (p : DensePoly R) (A : Matrix R n n) : Matrix R n n :=
  p.toArray.foldr
    (fun coefficient accumulator =>
      Matrix.mulImpl accumulator A + coefficient • Matrix.identity n)
    0

/-- The executable Horner loop agrees with the kernel-facing matrix
evaluation specification. -/
theorem evalMatrix_eq_evalMatrixImpl (p : DensePoly R) (A : Matrix R n n) :
    evalMatrix p A = evalMatrixImpl p A := by
  unfold evalMatrix evalMatrixImpl
  rw [← Array.foldr_toList]
  change DensePoly.evalCoeffList
      (p.toList.map fun c => c • Matrix.identity n) A =
    p.toList.foldr
      (fun coefficient accumulator =>
        Matrix.mulImpl accumulator A + coefficient • Matrix.identity n) 0
  induction p.toList with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp only [List.map_cons, DensePoly.evalCoeffList, List.foldr_cons]
      rw [ih]
      change Matrix.mul _ A + coefficient • Matrix.identity n =
        Matrix.mulImpl _ A + coefficient • Matrix.identity n
      rw [mul_eq_mulImpl]

/-- Register the array-backed Horner loop as the compiled implementation. -/
@[csimp]
theorem evalMatrix_eq_impl : @evalMatrix = @evalMatrixImpl := by
  funext R _ _ n p A
  exact evalMatrix_eq_evalMatrixImpl p A

end Hex.Matrix
