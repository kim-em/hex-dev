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
entry with zero.  Keeping it generic over the coefficient type lets the
integer and polynomial Smith-normal-form libraries share the constructor.
-/

namespace Hex

universe u

namespace Matrix

/-- The `n × m` matrix carrying `d` down its leading diagonal. Entries past
the length of `d`, and all off-diagonal entries, are zero. -/
@[expose]
def diagMatrix {R : Type u} [Zero R] {r : Nat} (d : Vector R r) (n m : Nat) :
    Matrix R n m :=
  Matrix.ofFn fun i j =>
    if h : i.val = j.val ∧ i.val < r then d[i.val]'h.2 else 0

/-- An entry of `diagMatrix` on its represented diagonal is the corresponding
vector entry. -/
@[simp, grind =]
theorem getElem_diagMatrix_of_eq {R : Type u} [Zero R] {r n m : Nat}
    (d : Vector R r) (i : Fin n) (j : Fin m) (hij : i.val = j.val)
    (hir : i.val < r) :
    (diagMatrix d n m)[i][j] = d[i.val]'hir := by
  rw [diagMatrix, getElem_ofFn]
  rw [dite_eq_left ⟨hij, hir⟩]

/-- An off-diagonal entry of `diagMatrix` is zero. -/
@[simp, grind =]
theorem getElem_diagMatrix_of_ne {R : Type u} [Zero R] {r n m : Nat}
    (d : Vector R r) (i : Fin n) (j : Fin m) (hij : i.val ≠ j.val) :
    (diagMatrix d n m)[i][j] = 0 := by
  rw [diagMatrix, getElem_ofFn]
  simp [hij]

/-- A diagonal entry past the represented vector is zero. -/
@[simp, grind =]
theorem getElem_diagMatrix_of_ge {R : Type u} [Zero R] {r n m : Nat}
    (d : Vector R r) (i : Fin n) (j : Fin m) (hir : r ≤ i.val) :
    (diagMatrix d n m)[i][j] = 0 := by
  rw [diagMatrix, getElem_ofFn]
  simp [Nat.not_lt.mpr hir]

end Matrix

end Hex
