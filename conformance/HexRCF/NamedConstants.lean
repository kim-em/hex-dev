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
namespace Hex.RCF.NamedConstants
open RealCoefficients Hex.OrderedFn.Oracle
set_option Elab.async false

-- Caller-supplied fixed bounds from existing theorems. These callbacks do
-- not promise the requested width, convergence or transcendence evidence.
@[expose] def piBounds (_ : Rat) : Bounds := ⟨3, mkRat 63 20, by norm_num⟩
@[expose] def expBounds (_ : Rat) : Bounds :=
  ⟨mkRat 5 2, mkRat 11 4, by norm_num⟩

@[rcf_constant, expose] def piRegistration : Registration Real.pi where
  version := 1
  approximation := piBounds
  containment δ _ := by
    norm_num [Contains, piBounds]
    constructor
    · exact Real.pi_gt_three.le
    · linarith [Real.pi_lt_d2]

@[rcf_constant, expose] def expRegistration : Registration (Real.exp 1) where
  version := 1
  approximation := expBounds
  containment δ _ := by
    norm_num [Contains, expBounds]
    constructor
    · linarith [Real.exp_one_gt_d9]
    · linarith [Real.exp_one_lt_d9]

theorem pi_square : ∀ x : ℝ, x ^ 2 > Real.pi - 4 := by rcf
theorem exp_square : ∀ x : ℝ, x ^ 2 + Real.exp 1 > 2 := by rcf
theorem exp_witness : ∃ x : ℝ, x = Real.exp 1 ∧ 2 < x ∧ x < 3 := by rcf
theorem pi_inverse : ∀ x : ℝ, x ^ 2 + 1 / (4 - Real.pi) > 0 := by rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + 0 / (Real.pi - Real.pi) ≥ 0 := by rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + (Real.pi - Real.pi) / (Real.pi - Real.pi) ≥ 0 := by rcf

-- A zero-containing enclosure supplies neither a strict sign nor equality.
@[irreducible] noncomputable def unknown : ℝ := Real.pi
@[expose] def unknownBounds (_ : Rat) : Bounds := ⟨-4, 4, by decide⟩
@[rcf_constant, expose] def unknownRegistration : Registration unknown where
  version := 1
  approximation := unknownBounds
  containment δ _ := by
    norm_num only [Contains, unknownBounds, unknown, Rat.cast_neg, Rat.cast_ofNat]
    constructor
    · linarith [Real.pi_pos]
    · exact Real.pi_lt_four.le

example : True := by
  fail_if_success
    have : ∀ x : ℝ, x ^ 2 + unknown > 0 := by rcf
  trivial

/-- error: rcf: original closed divisor remains unresolved in supplied bounds -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + 0 / unknown ≥ 0 := by rcf

end Hex.RCF.NamedConstants

/-- info: 'Hex.RCF.NamedConstants.pi_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.NamedConstants.pi_square
/-- info: 'Hex.RCF.NamedConstants.exp_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.NamedConstants.exp_square
/-- info: 'Hex.RCF.NamedConstants.exp_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.NamedConstants.exp_witness
/-- info: 'Hex.RCF.NamedConstants.pi_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.NamedConstants.pi_inverse
