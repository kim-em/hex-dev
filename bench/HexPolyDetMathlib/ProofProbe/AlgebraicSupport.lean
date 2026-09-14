/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.QuadraticAlgebra.Basic
namespace ClosedAlgebraic
abbrev K := QuadraticAlgebra Rat 2 0
@[irreducible] def α : K := QuadraticAlgebra.omega
theorem square : α ^ 2 = 2 := by
  rw [α, pow_two, QuadraticAlgebra.omega_mul_omega_eq_mk]
  rfl
end ClosedAlgebraic
