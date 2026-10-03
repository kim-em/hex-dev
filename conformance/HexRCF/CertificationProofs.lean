/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public import HexRCF.CertificationInputs
public meta import HexRCF.RealCoefficients
public meta import HexRCF.CertificationInputs
public meta import Lean.Elab.Tactic

public section
namespace Hex.RCF.CertificationProofs
open RealCoefficients CertificationInputs

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

theorem compound_positive : ∀ x : ℝ,
    x ^ 2 + (realAlgebraic.toReal ^ 2 + 1) > 0 := by rcf

abbrev fieldValue : RealAlgebraicNumber :=
  Coefficients.ofField realAlgebraic (realAlgebraic.toAlgebraic.toQAdjoin ^ 2 + 1)

theorem coordinate_positive : ∀ x : ℝ, x ^ 2 + fieldValue.toReal > 0 := by rcf

theorem guarded_positive : ∀ x : ℝ,
    x ^ 2 + 1 / realAlgebraic.toReal > 0 := by rcf

theorem further_root : ∃ x : ℝ,
    x ^ 2 = realAlgebraic.toReal ∧ 1 < x ∧ x < 2 := by rcf

theorem normalized_positive : ∀ x : ℝ,
    x ^ 2 + (normalized.toReal ^ 2 + 1) > 0 := by rcf

-- Exercise failures without leaving failed declarations or proof admissions.
local elab "expect_certificate_error " message:str : tactic => do
  let saved ← Lean.Elab.Tactic.saveState
  let observed ← try
    Lean.Elab.Tactic.evalTactic (← `(tactic| rcf))
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  saved.restore
  unless observed == some message.getString do
    throwError "unexpected rcf result: {observed}"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact False.elim (by assumption)))

example (_impossible : False) : ∀ x : ℝ, x ^ 2 + realAlgebraic.toReal < 0 := by
  expect_certificate_error "rcf: the universal sentence is false on the prepared cells"

example (_impossible : False) : ∀ x : ℝ,
    x ^ 2 + 0 / (realAlgebraic.toReal - realAlgebraic.toReal) ≥ 0 := by
  expect_certificate_error "rcf: original closed divisor is zero"

end Hex.RCF.CertificationProofs

/-- info: 'Hex.RCF.CertificationProofs.compound_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationProofs.compound_positive

/-- info: 'Hex.RCF.CertificationProofs.coordinate_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationProofs.coordinate_positive

/-- info: 'Hex.RCF.CertificationProofs.guarded_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationProofs.guarded_positive

/-- info: 'Hex.RCF.CertificationProofs.further_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationProofs.further_root

/-- info: 'Hex.RCF.CertificationProofs.normalized_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationProofs.normalized_positive
