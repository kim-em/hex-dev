/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdeal
public import HexDeterminantMathlib

public section

/-!
Transport of the executable minors to Mathlib: an entrywise map is
`Matrix.map`, a selected submatrix is `Matrix.submatrix`, an executable minor
is the Mathlib determinant of that submatrix, and a ring homomorphism passes
through the whole enumeration (`map_minors`), which is the only place a
homomorphism property is used.
-/

namespace HexDeterminantalIdealMathlib

open HexMatrixMathlib

universe u v

variable {R : Type u} {S : Type v} {n m : Nat}

/-- An entrywise map transports to `Matrix.map`. -/
@[simp, grind =] theorem matrixEquiv_map (A : Hex.Matrix R n m) (f : R → S) :
    matrixEquiv (A.map f) = (matrixEquiv A).map f := by
  ext i j
  rw [matrixEquiv_apply, Hex.Matrix.getElem_map, Matrix.map_apply, matrixEquiv_apply]

/-- A selected submatrix transports to `Matrix.submatrix` along the tuples. -/
@[simp, grind =] theorem matrixEquiv_selectedSubmatrix {k : Nat} (A : Hex.Matrix R n m)
    (rows : Vector (Fin n) k) (cols : Vector (Fin m) k) :
    matrixEquiv (Hex.Matrix.selectedSubmatrix A rows cols) =
      (matrixEquiv A).submatrix rows.get cols.get := by
  ext i j
  rw [matrixEquiv_apply, Hex.Matrix.getElem_selectedSubmatrix, Matrix.submatrix_apply,
    matrixEquiv_apply]
  rfl

/-- An executable minor is the Mathlib determinant of the selected submatrix. -/
theorem det_selectedSubmatrix_eq [CommRing R] {k : Nat} (A : Hex.Matrix R n m)
    (rows : Vector (Fin n) k) (cols : Vector (Fin m) k) :
    Hex.Matrix.det (Hex.Matrix.selectedSubmatrix A rows cols) =
      ((matrixEquiv A).submatrix rows.get cols.get).det := by
  rw [det_eq, matrixEquiv_selectedSubmatrix]

/-- A ring homomorphism passes through the enumeration of minors. -/
theorem map_minors [CommRing R] [CommRing S] (φ : R →+* S) (A : Hex.Matrix R n m) (r : Nat) :
    (Hex.Matrix.minors r A).map φ = Hex.Matrix.minors r (A.map φ) := by
  unfold Hex.Matrix.minors
  rw [List.map_flatMap]
  congr 1
  funext rows
  rw [List.map_map]
  congr 1
  funext cols
  simp only [Function.comp]
  rw [det_selectedSubmatrix_eq, det_selectedSubmatrix_eq, RingHom.map_det,
    RingHom.mapMatrix_apply, matrixEquiv_map, Matrix.submatrix_map]

end HexDeterminantalIdealMathlib
