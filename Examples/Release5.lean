/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib
public import HexRealRootsMathlib

public section

/-!
# Release 5: certified complex and real roots

The complex API is total once the caller supplies the mathematically necessary
nonzero and squarefree hypotheses.  The real-root elaborator also handles
non-squarefree inputs, returning one interval for each distinct real root.
-/

namespace Examples.Release5

open Hex Polynomial HexRootsMathlib HexRealRootsMathlib

/-- `x³ - x - 1`. -/
def complexInput : ZPoly :=
  DensePoly.monomial 3 1 - DensePoly.monomial 1 1 - DensePoly.C 1

theorem complexInput_poly :
    HexRootsMathlib.toPolyℂ complexInput = X ^ 3 - X - 1 := by
  simp [complexInput, HexRootsMathlib.toPolyℂ,
    monomial_one_right_eq_X_pow]

theorem complexInput_rat :
    HexPolyZMathlib.toPolyℚ complexInput = X ^ 3 - X - 1 := by
  simp [complexInput, HexPolyZMathlib.toPolyℚ, monomial_one_right_eq_X_pow]

theorem complexInput_degree :
    (HexRootsMathlib.toPolyℂ complexInput).natDegree = 3 := by
  rw [complexInput_poly,
    natDegree_sub_eq_left_of_natDegree_lt (by
      rw [natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num),
    natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num

theorem complexInput_ne : complexInput ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ZPoly => p.coeff 3) h
  norm_num [complexInput] at hcoeff

theorem complexInput_simple : HasOnlySimpleRoots complexInput := by
  rw [hasOnlySimpleRoots_iff_separable complexInput complexInput_ne,
    complexInput_rat, separable_def']
  let a : Polynomial ℚ := 18 * X - 27
  let b : Polynomial ℚ := -(6 * X ^ 2) + 9 * X + 4
  have hbezout :
      a * (X ^ 3 - X - 1) + b * derivative (X ^ 3 - X - 1) = 23 := by
    simp only [a, b, derivative_sub, derivative_pow, derivative_X,
      derivative_one, map_natCast]
    ring
  refine ⟨C (23⁻¹) * a, C (23⁻¹) * b, ?_⟩
  calc
    _ = C (23⁻¹) *
        (a * (X ^ 3 - X - 1) + b * derivative (X ^ 3 - X - 1)) := by ring
    _ = C (23⁻¹) * 23 := by rw [hbezout]
    _ = C (23⁻¹) * C 23 := by rw [C_ofNat]
    _ = C (23⁻¹ * 23) := by rw [map_mul]
    _ = 1 := by norm_num

/-- A none-free array of certified, pairwise-disjoint complex-root atoms. -/
noncomputable def complexRoots :=
  HexRootsMathlib.isolate! complexInput complexInput_simple complexInput_ne 32

example : complexRoots.size = 3 := by
  rw [show complexRoots.size =
      (HexRootsMathlib.toPolyℂ complexInput).natDegree by
    simpa [complexRoots] using
    HexRootsMathlib.isolate!_count complexInput complexInput_simple
      complexInput_ne 32]
  exact complexInput_degree

/-- A repeated-root input: the output contains the two distinct real roots
`1` and `3`, not three multiplicity-expanded entries. -/
noncomputable def realRoots :=
  isolate_roots ((X - 1) ^ 2 * (X - 3) : Polynomial ℤ)

example : realRoots.intervals =
    #v[((0 : ℚ), (2 : ℚ)), ((2 : ℚ), (4 : ℚ))] := rfl

end Examples.Release5
