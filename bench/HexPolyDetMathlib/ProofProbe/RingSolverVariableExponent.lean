/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic

theorem result (x : Int) (k : Nat) : (x ^ k) * (x ^ k) = x ^ (2 * k) := by
  fail_if_success grobner
  rw [two_mul, pow_add]

#print axioms result
