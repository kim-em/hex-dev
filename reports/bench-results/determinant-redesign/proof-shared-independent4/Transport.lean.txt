/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tree

namespace Determinant

theorem mapRows (f : R → S) (a : Fin n → R) (as : Fin m → Fin n → R) :
    (Matrix.of (Matrix.vecCons a as)).map f =
      Matrix.of (Matrix.vecCons (f ∘ a) ((Matrix.of as).map f)) := by
  ext i j
  cases i using Fin.cases <;> rfl

theorem mapEmpty (f : R → S) :
    (Matrix.of ![] : Matrix (Fin 0) (Fin n) R).map f = Matrix.of ![] := by
  ext i
  exact i.elim0

theorem compCons (f : R → S) (a : R) (as : Fin n → R) :
    f ∘ Matrix.vecCons a as = Matrix.vecCons (f a) (f ∘ as) := by
  funext i
  cases i using Fin.cases <;> rfl

theorem compEmpty (f : R → S) : f ∘ (![] : Fin 0 → R) = ![] := by
  funext i
  exact i.elim0

end Determinant
