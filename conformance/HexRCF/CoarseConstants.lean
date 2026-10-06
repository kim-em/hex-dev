/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

public section
namespace Hex.RCF.CoarseConstants
open RealCoefficients Hex.OrderedFn.Oracle
set_option Elab.async false

-- This fresh module has only coarse registrations. Refusal concerns supplied
-- evidence, not a mathematical assertion about independence of π and e.
@[expose] def bounds (_ : Rat) : Bounds := ⟨-4, 4, by decide⟩

@[rcf_constant, expose] def piRegistration : Registration Real.pi where
  version := 1
  approximation := bounds
  containment δ _ := by
    norm_num only [Contains, bounds, Rat.cast_neg, Rat.cast_ofNat]
    constructor
    · linarith [Real.pi_pos]
    · exact Real.pi_lt_four.le

@[rcf_constant, expose] def expRegistration : Registration (Real.exp 1) where
  version := 1
  approximation := bounds
  containment δ _ := by
    norm_num only [Contains, bounds, Rat.cast_neg, Rat.cast_ofNat]
    constructor
    · linarith [Real.exp_pos (1 : ℝ)]
    · linarith [Real.exp_one_lt_three]

/-- error: rcf: original closed divisor remains unresolved in supplied bounds -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + 0 / (Real.pi ^ 2 - Real.exp 1 ^ 3) ≥ 0 := by rcf

/-- error: rcf: original closed divisor remains unresolved in supplied bounds -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + 0 / Real.pi ≥ 0 := by rcf

end Hex.RCF.CoarseConstants
