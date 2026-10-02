/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Support

public section

namespace Hex.SignDet

/-- A dimension-indexed Cartesian product with the same concatenation order
as `product`. The matrix adapter uses this form to expose its two indices. -/
@[expose] def productVector {r s : Nat} (xs : Vector (List α) r) (ys : Vector (List α) s) :
    Vector (List α) (r * s) :=
  Vector.ofFn fun i =>
    xs[(⟨i.val / s, Matrix.row_of_lt i⟩ : Fin r)] ++
      ys[(⟨i.val % s, Matrix.col_of_lt i⟩ : Fin s)]

/-- Kronecker product of integer witnesses, in the same left-major order as
the Cartesian product of BKR supports and exponent rows. -/
@[expose] def tensor {r s : Nat} (a : Matrix Int r r) (b : Matrix Int s s) :
    Matrix Int (r * s) (r * s) :=
  Matrix.ofFn fun i j =>
    a[((⟨i.val / s, Matrix.row_of_lt i⟩ : Fin r), (⟨j.val / s, Matrix.row_of_lt j⟩ : Fin r))] *
    b[((⟨i.val % s, Matrix.col_of_lt i⟩ : Fin s), (⟨j.val % s, Matrix.col_of_lt j⟩ : Fin s))]

end Hex.SignDet
