/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLLMathlib.Bridge
public import HexLLLMathlib.Reducer
public import HexLLL.Basic

public section

/-!
The headline Mathlib capstones: the unconditional Euclidean short-vector
bounds `lll_first_row_norm_sq_le_unconditional` (at `η = 11/20`) and
`lllNative_first_row_norm_sq_le_unconditional` (classical `η = 1/2`), and the
submodule lattice-preservation transfers `lll_mem_latticeSubmodule_iff` and
`lllNative_mem_latticeSubmodule_iff`.
-/

namespace HexLLLMathlib

/-- Membership in the Mathlib `latticeSubmodule` is preserved by
`Hex.lllNative`. -/
theorem lllNative_mem_latticeSubmodule_iff
    (b : Hex.Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (x : Fin m → ℤ) :
    x ∈ latticeSubmodule (Hex.lllNative b δ hδ hδ' hn) ↔ x ∈ latticeSubmodule b := by
  let v := HexMatrixMathlib.vectorEquiv.symm x
  have hxv : x = HexMatrixMathlib.vectorEquiv v :=
    (Equiv.apply_symm_apply _ x).symm
  rw [hxv]
  rw [mem_latticeSubmodule_iff (Hex.lllNative b δ hδ hδ' hn) v,
      mem_latticeSubmodule_iff b v]
  exact Hex.lllNative_memLattice_iff b δ hδ hδ' hn v

/-- Membership in the Mathlib `latticeSubmodule` is preserved by `Hex.lll`. -/
theorem lll_mem_latticeSubmodule_iff
    (b : Hex.Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hind : b.independent) (x : Fin m → ℤ) :
    x ∈ latticeSubmodule (Hex.lll b δ hδ hδ' hn hind) ↔ x ∈ latticeSubmodule b := by
  let v := HexMatrixMathlib.vectorEquiv.symm x
  have hxv : x = HexMatrixMathlib.vectorEquiv v :=
    (Equiv.apply_symm_apply _ x).symm
  rw [hxv]
  rw [mem_latticeSubmodule_iff (Hex.lll b δ hδ hδ' hn hind) v,
      mem_latticeSubmodule_iff b v]
  exact Hex.lll_memLattice_iff b δ hδ hδ' hn hind v

/-- Classical Mathlib-Euclidean LLL short-vector bound on `Hex.lllNative` at
`η = 1/2`. Combines `Hex.lllNative_isLLLReduced` with the conditional
Euclidean bound `reduced_first_row_norm_sq_le` at
`η = 1/2`. -/
theorem lllNative_first_row_norm_sq_le_unconditional
    (b : Hex.Matrix Int n m) (δ : Rat)
    (hδ : (1 : Rat) / 4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hind : b.independent)
    (x : Fin m → ℤ) (hx : x ∈ latticeSubmodule b) (hx0 : x ≠ 0) :
    ‖intRowToEuclidean
        (Hex.Matrix.row (Hex.lllNative b δ hδ hδ' hn)
          ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩)‖ ^ 2 ≤
      (((1 / (δ - 1 / 4)) ^ (n - 1) : Rat) : ℝ) *
        ‖intVectorToEuclidean x‖ ^ 2 := by
  have hred : Hex.isLLLReduced (Hex.lllNative b δ hδ hδ' hn) δ (1 / 2) :=
    Hex.lllNative_isLLLReduced b δ hδ hδ' hn hind
  have hind' : (Hex.lllNative b δ hδ hδ' hn).independent :=
    Hex.lllNative_independent b δ hδ hδ' hn hind
  have hx_lll : x ∈ latticeSubmodule (Hex.lllNative b δ hδ hδ' hn) :=
    (lllNative_mem_latticeSubmodule_iff b δ hδ hδ' hn x).mpr hx
  have hbnd := reduced_first_row_norm_sq_le
    (Hex.lllNative b δ hδ hδ' hn) δ (1 / 2) (by grind) (by grind) hδ' hn hind'
    hred x hx_lll hx0
  -- Rewrite `(1/2) * (1/2)` as `1/4` in the bound's denominator.
  have hηη : (1 / 2 : Rat) * (1 / 2) = 1 / 4 := by grind
  rw [hηη] at hbnd
  exact hbnd

/-- **Unconditional Mathlib-Euclidean LLL short-vector bound on `Hex.lll` at
`η = 11/20`.** Combines `Hex.lll_isLLLReduced` (η = 11/20) with the
conditional Euclidean bound `reduced_first_row_norm_sq_le`
at `η = 11/20`. -/
theorem lll_first_row_norm_sq_le_unconditional
    (b : Hex.Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hind : b.independent)
    (x : Fin m → ℤ) (hx : x ∈ latticeSubmodule b) (hx0 : x ≠ 0) :
    ‖intRowToEuclidean
        (Hex.Matrix.row (Hex.lll b δ hδ hδ' hn hind)
          ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩)‖ ^ 2 ≤
      (((1 / (δ - 121 / 400)) ^ (n - 1) : Rat) : ℝ) *
        ‖intVectorToEuclidean x‖ ^ 2 := by
  have hred : Hex.isLLLReduced (Hex.lll b δ hδ hδ' hn hind) δ (11 / 20) :=
    Hex.lll_isLLLReduced b δ hδ hδ' hn hind
  have hind' : (Hex.lll b δ hδ hδ' hn hind).independent :=
    Hex.lll_independent b δ hδ hδ' hn hind
  have hx_lll : x ∈ latticeSubmodule (Hex.lll b δ hδ hδ' hn hind) :=
    (lll_mem_latticeSubmodule_iff b δ hδ hδ' hn hind x).mpr hx
  have hδη : (11 / 20 : Rat) * (11 / 20) < δ := by
    have : (11 / 20 : Rat) * (11 / 20) = 121 / 400 := by grind
    grind
  have hbnd := reduced_first_row_norm_sq_le
    (Hex.lll b δ hδ hδ' hn hind) δ (11 / 20) (by grind) hδη hδ' hn hind'
    hred x hx_lll hx0
  have hηη : (11 / 20 : Rat) * (11 / 20) = 121 / 400 := by grind
  simpa [hηη] using hbnd

end HexLLLMathlib
