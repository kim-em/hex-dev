/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients

namespace Hex.RCF.TotalAlgebraicProofs

open Lean Elab Tactic

-- Assert the diagnostic without adding a failed theorem declaration or an admission.
elab "expect_rcf_error " message:str : tactic => do
  let saved ← saveState
  let observed ← try
    evalTactic (← `(tactic| rcf))
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  saved.restore
  unless observed == some message.getString do
    throwError "unexpected rcf result: {observed}"
  evalTactic (← `(tactic| exact False.elim (by assumption)))


set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

-- A source goal with two carrier roots closer than the old bounded direct
-- bisection depth. The prepared-sign producer can separate them directly;
-- the separate IsolationProgress module exercises actual canonical fallback.
theorem close_sections : ∃ x : ℝ,
    x = Real.sqrt 2 ∧ x < Real.sqrt 2 + 1 / (5444517870735015415413993718908291383296 : ℝ) := by
  rcf

theorem further_section : ∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by rcf

theorem repeated_nonnegative : ∀ x : ℝ,
    x ^ 2 - 2 * Real.sqrt 2 * x + 2 ≥ 0 := by rcf

theorem closed_power : ∀ x : ℝ, x ^ 2 + (Real.sqrt 2) ^ 3 > 0 := by rcf

theorem closed_guard : ∀ x : ℝ,
    x / (Real.sqrt 2 + 2) = (1 / (Real.sqrt 2 + 2)) * x := by rcf


example (_impossible : False) : ∀ x : ℝ, x ^ 2 < Real.sqrt 2 := by
  expect_rcf_error "rcf: the universal sentence is false on the prepared cells"

-- Lean defines division by zero, but this extension rejects every original zero divisor.
example (_impossible : False) : ∀ _x : ℝ, 0 / (Real.sqrt 2 - Real.sqrt 2) = 0 := by
  expect_rcf_error "rcf: original closed divisor is zero"

-- A quoted proof through the same prepared-sign fallback used by the tactic.
set_option rcf.algebraic.directDepth 0 in
theorem canonical_sections : ∃ x : ℝ, x = Real.sqrt 2 ∧ x ≠ 0 := by rcf

set_option rcf.algebraic.directDepth 0 in
theorem canonical_close_sections : ∃ x : ℝ, x = Real.sqrt 2 ∧
    x < Real.sqrt 2 + 1 / (5444517870735015415413993718908291383296 : ℝ) := by rcf

set_option rcf.algebraic.directDepth 0 in
set_option rcf.algebraic.maxDoublings 0 in
example (_impossible : False) : ∃ x : ℝ, x = Real.sqrt 2 ∧ x ≠ 0 := by
  expect_rcf_error "rcf: algebraic interval refinement budget exhausted; increase rcf.algebraic.maxDoublings or rcf.algebraic.directDepth"

end Hex.RCF.TotalAlgebraicProofs

/-- info: '_private.HexRCF.TotalAlgebraicProofs.0.Hex.RCF.TotalAlgebraicProofs.close_sections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.TotalAlgebraicProofs.close_sections
/-- info: '_private.HexRCF.TotalAlgebraicProofs.0.Hex.RCF.TotalAlgebraicProofs.further_section' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.TotalAlgebraicProofs.further_section
/-- info: '_private.HexRCF.TotalAlgebraicProofs.0.Hex.RCF.TotalAlgebraicProofs.repeated_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.TotalAlgebraicProofs.repeated_nonnegative
/-- info: '_private.HexRCF.TotalAlgebraicProofs.0.Hex.RCF.TotalAlgebraicProofs.closed_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.TotalAlgebraicProofs.closed_power
/-- info: '_private.HexRCF.TotalAlgebraicProofs.0.Hex.RCF.TotalAlgebraicProofs.closed_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.TotalAlgebraicProofs.closed_guard

/-- info: '_private.HexRCF.TotalAlgebraicProofs.0.Hex.RCF.TotalAlgebraicProofs.canonical_sections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.TotalAlgebraicProofs.canonical_sections

/-- info: '_private.HexRCF.TotalAlgebraicProofs.0.Hex.RCF.TotalAlgebraicProofs.canonical_close_sections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.TotalAlgebraicProofs.canonical_close_sections
