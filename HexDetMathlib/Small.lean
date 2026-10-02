/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDet
public import HexDeterminantMathlib

public section

/-!
The small arm.

`Hex.Det.small?` returns the closed determinant forms at `n = 0`, `1` and `2`.
These are the reference determinant's own closed forms from
`HexDeterminant/Leibniz.lean`, so no characteristic polynomial is computed to
establish them.
-/

namespace HexDetMathlib

open Hex.Det

universe u

variable {R : Type u} [Lean.Grind.CommRing R] {n : Nat}

/-! The size lemmas the interpreter's branch structure rests on. -/

/-- The determinant of an empty matrix is one. -/
theorem det_empty (A : Hex.Matrix R 0 0) : Hex.Matrix.det A = 1 := by
  have h := Hex.Matrix.det_principalSubmatrix_zero (R := R) (n := 0) A
  rwa [show Hex.Matrix.principalSubmatrix A 0 (Nat.zero_le 0) = A from
    Hex.Matrix.ext (Vector.ext fun _ hi => absurd hi (by omega))] at h

/-- The small arm applies exactly at the sizes it has closed forms for. -/
theorem le_two_of_small?_eq_some {A : Hex.Matrix R n n} {value : R}
    (h : small? A = some value) : n ≤ 2 := by
  match n, A with
  | 0, _ | 1, _ | 2, _ => omega
  | _ + 3, _ => simp [small?] at h

/-- Above the small sizes the interpreter runs the recipe's own arm. -/
theorem small?_eq_none_of_three_le {A : Hex.Matrix R n n} (h : 3 ≤ n) :
    small? A = none := by
  match n, A with
  | 0, _ | 1, _ | 2, _ => omega
  | _ + 3, _ => rfl

/-- The small arm returns the reference determinant. -/
theorem eq_det_of_small?_eq_some {A : Hex.Matrix R n n} {value : R}
    (h : small? A = some value) : value = Hex.Matrix.det A := by
  match n, A with
  | 0, A =>
      rw [det_empty]
      exact (Option.some.inj h).symm
  | 1, A =>
      rw [← Option.some.inj h]
      simp
  | 2, A =>
      rw [← Option.some.inj h]
      simp
      grind
  | _ + 3, _ => simp [small?] at h

end HexDetMathlib
