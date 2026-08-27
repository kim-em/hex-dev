/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLLMathlib.ReductionInvariant

public section

/-!
Reducedness, lattice preservation, independence, and short-vector bounds for
native and externally accelerated LLL reduction.
-/

namespace Hex

open Hex.Internal

/-! # Public correctness theorems

The unconditional LLL guarantees split across two surfaces:

* **Native** (`Hex.lllNative`, classical bound, precondition `1/4 < δ`).
  Carries `isLLLReduced … δ (1/2)` because the integer size-reduction step
  inside the loop produces exact `|μ| ≤ 1/2`. The short-vector denominator
  is `δ − 1/4`.
* **Public** (`Hex.lll`, precondition `121/400 < δ`). Wraps `lllNative` and
  carries `isLLLReduced … δ (11/20)` (the η = 1/2 native bound weakens to
  η = 11/20 by `isLLLReduced.mono_η`). The short-vector denominator is
  `δ − 121/400`. This is the uniform bound an external reducer can promise. -/

/-- The native LLL body produces a `(δ, 1/2)`-LLL-reduced matrix. Combines the
fuel-sufficiency theorem (`lllLoop_fuel_sufficient`) with the loop invariant
induction (`lllLoop_isLLLReduced_of_fuel_gt_measure`). -/
theorem lllNative_isLLLReduced (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hind : b.independent) :
    isLLLReduced (lllNative b δ hδ hδ' hn) δ (1 / 2) := by
  show isLLLReduced (lllLoop (LLLState.ofBasis b) 1 δ hδ hδ'
    (Nat.le_refl 1) hn (lllFuel (LLLState.ofBasis b))) δ (1 / 2)
  set s := LLLState.ofBasis b with hs_def
  have hs_valid : s.Valid := by
    show (LLLState.ofBasis b).Valid
    exact HexLLLMathlib.LLLState.ofBasis_valid b
  have hs_ind : s.b.independent := hind
  have hs_pre : prefixLLLReduced s.b 1 δ := prefixLLLReduced_one s.b δ
  apply LLLState.lllLoop_isLLLReduced_of_fuel_gt_measure δ hδ hδ' (lllFuel s) s 1
    (Nat.le_refl 1) hn hs_valid hs_ind hs_pre
  show s.potential * (n + 1) + (n - 1) < (s.potential + 1) * (n + 1)
  have : (s.potential + 1) * (n + 1) = s.potential * (n + 1) + (n + 1) := by ring
  omega

/-- The generated lattice is preserved by `Hex.lllNative`. -/
@[simp]
theorem lllNative_memLattice_iff (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (v : Vector Int m) :
    Matrix.memLattice (lllNative b δ hδ hδ' hn) v ↔ Matrix.memLattice b v := by
  show Matrix.memLattice (lllLoop (LLLState.ofBasis b) 1 δ hδ hδ'
    (Nat.le_refl 1) hn (lllFuel (LLLState.ofBasis b))) v ↔ _
  exact lllLoop_memLattice_iff _ 1 δ hδ hδ' (Nat.le_refl 1) hn _ v

/-- Independence is preserved by `Hex.lllNative`. -/
theorem lllNative_independent (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hind : b.independent) :
    (lllNative b δ hδ hδ' hn).independent := by
  have hs_valid : (LLLState.ofBasis b).Valid :=
    HexLLLMathlib.LLLState.ofBasis_valid b
  show (lllLoop (LLLState.ofBasis b) 1 δ hδ hδ'
    (Nat.le_refl 1) hn (lllFuel (LLLState.ofBasis b))).independent
  exact LLLState.lllLoop_independent δ hδ hδ' _ _ 1
    (Nat.le_refl 1) hn hs_valid hind

/-- Classical native LLL short-vector bound at `η = 1/2`. For any independent
integer basis `b`, the first row of `Hex.lllNative b δ ...` has squared norm
at most `(1 / (δ − 1/4))^(n − 1)` times the squared norm of any nonzero
lattice vector. -/
theorem lllNative_short_vector
    (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hind : b.independent)
    {v : Vector Int m} (hv : Matrix.memLattice b v) (hv' : v ≠ 0) :
    ((((lllNative b δ hδ hδ' hn).row
        ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩).normSq : Int) : Rat) ≤
      (1 / (δ - 1 / 4)) ^ (n - 1) * ((v.normSq : Int) : Rat) := by
  have hred : isLLLReduced (lllNative b δ hδ hδ' hn) δ (1 / 2) :=
    lllNative_isLLLReduced b δ hδ hδ' hn hind
  have hind' : (lllNative b δ hδ hδ' hn).independent :=
    lllNative_independent b δ hδ hδ' hn hind
  have hv_lll : Matrix.memLattice (lllNative b δ hδ hδ' hn) v :=
    (lllNative_memLattice_iff b δ hδ hδ' hn v).mpr hv
  have hbnd := Hex.short_vector_bound_of_size_bound (lllNative b δ hδ hδ' hn) hind'
    hred (by grind) (by grind) hδ' hn hv_lll hv'
  -- Rewrite `(1/2) * (1/2)` as `1/4` in the resulting denominator.
  have hηη : (1 / 2 : Rat) * (1 / 2) = 1 / 4 := by grind
  rw [hηη] at hbnd
  exact hbnd

/-- Property triple for an accepted external reduction: a `B'` returned by
`ExternalReducer.certifiedReduction b δ` generates the same lattice as `b`, is independent,
and is `(δ, 11/20)`-LLL-reduced. Composes `certifiedReduction_some_certCheck` with
`HexLLLMathlib.certCheck_sound`, the single trusted property-level correspondence of
`hex-lll` §"Certified external selection". -/
theorem certifiedReduction_some_property {b : Matrix Int n m} {δ : Rat}
    {B' : Matrix Int n m} (h : ExternalReducer.certifiedReduction b δ = some B') :
    (∀ v, b.memLattice v ↔ B'.memLattice v) ∧
      B'.independent ∧ isLLLReduced B' δ (11 / 20) := by
  obtain ⟨U, V, hcheck⟩ := ExternalReducer.certifiedReduction_some_certCheck h
  exact HexLLLMathlib.certCheck_sound hcheck

/-- The public LLL `lll` produces a `(δ, 11/20)`-LLL-reduced matrix. On the
native path this is `lllNative_isLLLReduced` (`η = 1/2`) lifted to `η = 11/20`
by `isLLLReduced.mono_η`. On the certified-selection path it follows from
`certCheck_sound` via `certifiedReduction_some_property`. -/
theorem lll_isLLLReduced (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hind : b.independent) :
    isLLLReduced (lll b δ hδ hδ' hn) δ (11 / 20) := by
  unfold lll
  cases hd : ExternalReducer.certifiedReduction b δ with
  | none =>
      exact Hex.Internal.isLLLReduced.mono_η _ (by grind) (by grind)
        (lllNative_isLLLReduced b δ
          (Hex.Internal.one_quarter_lt_of_eta_eleven_twentieths hδ) hδ' hn hind)
  | some B' =>
      exact (certifiedReduction_some_property hd).2.2

/-- The generated lattice is preserved by `Hex.lll`. -/
@[simp]
theorem lll_memLattice_iff (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (v : Vector Int m) :
    Matrix.memLattice (lll b δ hδ hδ' hn) v ↔ Matrix.memLattice b v := by
  unfold lll
  cases hd : ExternalReducer.certifiedReduction b δ with
  | none =>
      exact lllNative_memLattice_iff b δ
        (Hex.Internal.one_quarter_lt_of_eta_eleven_twentieths hδ) hδ' hn v
  | some B' =>
      exact ((certifiedReduction_some_property hd).1 v).symm

/-- Independence is preserved by `Hex.lll`. -/
theorem lll_independent (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hind : b.independent) :
    (lll b δ hδ hδ' hn).independent := by
  unfold lll
  cases hd : ExternalReducer.certifiedReduction b δ with
  | none =>
      exact lllNative_independent b δ
        (Hex.Internal.one_quarter_lt_of_eta_eleven_twentieths hδ) hδ' hn hind
  | some B' =>
      exact (certifiedReduction_some_property hd).2.1

/-- Public LLL short-vector bound at `η = 11/20`. For any independent
integer basis `b`, the first row of `Hex.lll b δ …` has squared norm at
most `(1 / (δ − 121/400))^(n − 1)` times the squared norm of any nonzero
lattice vector. -/
theorem lll_short_vector
    (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hind : b.independent)
    {v : Vector Int m} (hv : Matrix.memLattice b v) (hv' : v ≠ 0) :
    ((((lll b δ hδ hδ' hn).row
        ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩).normSq : Int) : Rat) ≤
      (1 / (δ - 121 / 400)) ^ (n - 1) * ((v.normSq : Int) : Rat) := by
  have hred : isLLLReduced (lll b δ hδ hδ' hn) δ (11 / 20) :=
    lll_isLLLReduced b δ hδ hδ' hn hind
  have hind' : (lll b δ hδ hδ' hn).independent :=
    lll_independent b δ hδ hδ' hn hind
  have hv_lll : Matrix.memLattice (lll b δ hδ hδ' hn) v :=
    (lll_memLattice_iff b δ hδ hδ' hn v).mpr hv
  have hδη : (11 / 20 : Rat) * (11 / 20) < δ := by
    have : (11 / 20 : Rat) * (11 / 20) = 121 / 400 := by grind
    grind
  have hbnd := Hex.short_vector_bound_of_size_bound (lll b δ hδ hδ' hn)
    hind' hred (by grind) hδη hδ' hn hv_lll hv'
  have hηη : (11 / 20 : Rat) * (11 / 20) = 121 / 400 := by grind
  simpa [hηη] using hbnd

end Hex
