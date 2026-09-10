/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic

public section

/-!
Leading-diagonal matrix construction.

Unlike a square diagonal constructor, `diagMatrix d n m` embeds a vector in
the leading diagonal of an arbitrary rectangular matrix and fills every other
entry with zero. Keeping it generic over the coefficient type lets the
integer and polynomial Smith-normal-form libraries share the constructor.
-/

namespace Hex.Matrix

universe u

/-- The `n × m` matrix carrying `d` down its leading diagonal. Entries past
the length of `d`, and all off-diagonal entries, are zero. -/
@[expose]
def diagMatrix {R : Type u} [Zero R] {r : Nat} (d : Vector R r) (n m : Nat) :
    Matrix R n m :=
  Matrix.ofFn fun i j =>
    if h : i.val = j.val ∧ i.val < r then d[(⟨i.val, h.2⟩ : Fin r)] else 0

/-- Entry formula for `diagMatrix`. -/
@[grind =]
theorem getElem_diagMatrix {R : Type u} [Zero R] {r n m : Nat}
    (d : Vector R r) (i : Fin n) (j : Fin m) :
    (diagMatrix d n m)[i][j] =
      if h : i.val = j.val ∧ i.val < r then d[(⟨i.val, h.2⟩ : Fin r)] else 0 := by
  rw [diagMatrix, Matrix.getElem_ofFn]

/-- An entry of `diagMatrix` on its represented diagonal is the corresponding
vector entry. -/
@[simp, grind =]
theorem getElem_diagMatrix_of_eq {R : Type u} [Zero R] {r n m : Nat}
    (d : Vector R r) (i : Fin n) (j : Fin m) (hij : i.val = j.val)
    (hir : i.val < r) :
    (diagMatrix d n m)[i][j] = d[(⟨i.val, hir⟩ : Fin r)] := by
  rw [diagMatrix, Matrix.getElem_ofFn]
  rw [dite_eq_left ⟨hij, hir⟩]

/-- An off-diagonal entry of `diagMatrix` is zero. -/
@[simp, grind =]
theorem getElem_diagMatrix_of_ne {R : Type u} [Zero R] {r n m : Nat}
    (d : Vector R r) (i : Fin n) (j : Fin m) (hij : i.val ≠ j.val) :
    (diagMatrix d n m)[i][j] = 0 := by
  rw [getElem_diagMatrix]
  simp [hij]

/-- A diagonal entry past the represented vector is zero. -/
@[simp, grind =]
theorem getElem_diagMatrix_of_ge {R : Type u} [Zero R] {r n m : Nat}
    (d : Vector R r) (i : Fin n) (j : Fin m) (hir : r ≤ i.val) :
    (diagMatrix d n m)[i][j] = 0 := by
  rw [getElem_diagMatrix]
  simp [Nat.not_lt.mpr hir]

/-- Compatibility name for an off-diagonal entry of `diagMatrix`. -/
@[simp]
theorem diagMatrix_apply_of_ne {R : Type u} [Zero R] {r n m : Nat}
    (d : Vector R r) (i : Fin n) (j : Fin m) (hij : i.val ≠ j.val) :
    (diagMatrix d n m)[i][j] = 0 :=
  getElem_diagMatrix_of_ne d i j hij

/-- Compatibility name for a represented diagonal entry of `diagMatrix`. -/
@[simp]
theorem diagMatrix_apply_diag {R : Type u} [Zero R] {r n m : Nat}
    (d : Vector R r) (i : Fin n) (j : Fin m)
    (hij : i.val = j.val) (hir : i.val < r) :
    (diagMatrix d n m)[i][j] = d[(⟨i.val, hir⟩ : Fin r)] :=
  getElem_diagMatrix_of_eq d i j hij hir

/-- Compatibility name for a diagonal entry past the represented vector. -/
@[simp]
theorem diagMatrix_apply_of_ge {R : Type u} [Zero R] {r n m : Nat}
    (d : Vector R r) (i : Fin n) (j : Fin m) (hir : r ≤ i.val) :
    (diagMatrix d n m)[i][j] = 0 :=
  getElem_diagMatrix_of_ge d i j hir

/-- A row beyond the represented diagonal is zero. -/
@[simp]
theorem row_diagMatrix_of_ge {R : Type u} [Zero R] {r n m : Nat}
    (d : Vector R r) (i : Fin n) (hir : r ≤ i.val) :
    Matrix.row (diagMatrix d n m) i = 0 := by
  apply Vector.ext
  intro j hj
  let jj : Fin m := ⟨j, hj⟩
  change (diagMatrix d n m)[i][jj] = (0 : Vector R m)[j]
  rw [diagMatrix_apply_of_ge d i jj hir, Vector.getElem_zero]

/-- A represented row of a diagonal matrix is the corresponding scalar
multiple of an ambient unit vector. -/
theorem row_diagMatrix_cast {R : Type u} [Lean.Grind.Semiring R] {r n m : Nat}
    (d : Vector R r) (hrn : r ≤ n) (hrm : r ≤ m) (i : Fin r) :
    Matrix.row (diagMatrix d n m) (Fin.castLE hrn i) =
      d[i] • Vector.unit R (Fin.castLE hrm i) := by
  apply Vector.ext
  intro j hj
  let jj : Fin m := ⟨j, hj⟩
  change (diagMatrix d n m)[Fin.castLE hrn i][jj] =
    (d[i] • Vector.unit R (Fin.castLE hrm i))[j]
  rw [Vector.getElem_smul]
  change (diagMatrix d n m)[Fin.castLE hrn i][jj] =
    d[i] * (Vector.unit R (Fin.castLE hrm i))[jj]
  rw [Vector.getElem_unit]
  by_cases hij : Fin.castLE hrm i = jj
  · have hval : i.val = jj.val := by
      simpa only [Fin.castLE, Fin.mk.injEq] using congrArg Fin.val hij
    rw [ite_eq_left hij, diagMatrix_apply_diag d (Fin.castLE hrn i) jj hval i.isLt]
    have hd : d[(⟨(Fin.castLE hrn i).val, i.isLt⟩ : Fin r)] = d[i] := by
      exact congrArg (fun q : Fin r => d[q]) (Fin.ext rfl)
    rw [hd]
    exact (Lean.Grind.Semiring.mul_one d[i]).symm
  · have hval : i.val ≠ jj.val := by
      intro h
      apply hij
      exact Fin.ext h
    rw [ite_eq_right hij, diagMatrix_apply_of_ne d (Fin.castLE hrn i) jj hval]
    exact (Lean.Grind.Semiring.mul_zero d[i]).symm

end Hex.Matrix
