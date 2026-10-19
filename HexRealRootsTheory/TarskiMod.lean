/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRootsTheory.TarskiSum
public import Mathlib.Algebra.Polynomial.FieldDivision
import all HexRealRootsTheory.TarskiSum

public section

namespace HexRealRootsTheory.Tarski

open Hex Polynomial

/-- Reducing a query modulo its head preserves its signed sum at head roots,
including zero heads, repeated roots and infinite endpoints. -/
theorem rootSum_mod {R : Type*} [Field R] [LinearOrder R]
    (p q : Polynomial R) (a b : Endpoint R) :
    rootSum p (q % p) a b = rootSum p q a b := by
  classical
  unfold rootSum
  apply Finset.sum_congr rfl
  intro x hx
  have hz := (Polynomial.isRoot_of_mem_roots ((mem_rootsIn p a b x).mp hx).1).eq_zero
  rw [EuclideanDomain.mod_eq_sub_mul_div, Polynomial.eval_sub,
    Polynomial.eval_mul, hz, zero_mul, sub_zero]

end HexRealRootsTheory.Tarski
