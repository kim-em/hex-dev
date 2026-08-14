/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.SinTen

/-!
# Machin range-reduction conformance

The successful certificate produces an ordinary theorem. Endpoint mutations
exercise the bounded numeric adequacy gate; reduction and method mutations
remain exact fixed-canary refusals.
-/

namespace Hex.IntervalMathlib.SinTenConformance

open Hex.Interval.Experiment.SemanticReplay
open Hex.Interval.Experiment.SinTen
open Hex.IntervalMathlib.Experiment.SinTen

/-- A differently encoded provider enclosure with the same numeric bounds. -/
def rescaledConstant : ConstantCandidate :=
  { lowerNumerator := 6, lowerDenominator := 2,
    upperNumerator := 32, upperDenominator := 10 }

#guard Reduction.adequate Machin.candidate
#guard Reduction.adequate rescaledConstant
#guard !Reduction.adequate { Machin.candidate with lowerNumerator := 2 }
#guard !Reduction.adequate { Machin.candidate with lowerDenominator := 2 }
#guard !Reduction.adequate { Machin.candidate with upperNumerator := 17 }
#guard !Reduction.adequate { Machin.candidate with upperDenominator := 4 }
#guard !Reduction.adequate { Machin.candidate with lowerDenominator := 0 }
#guard !Reduction.adequate { Machin.candidate with upperDenominator := 0 }
#guard !Reduction.adequate { rescaledConstant with upperNumerator := 33 }

noncomputable def rescaledEvidence :
    Evidence (MachinReplay.Claim rescaledConstant) :=
  { proof := by
      change (6 : ℝ) / 2 < Real.pi ∧ Real.pi < (32 : ℝ) / 10
      convert MachinReplay.pi_bounds using 1 <;> norm_num }

example : Option.isSome
    (ReductionReplay.replay? rescaledConstant Reduction.candidate rescaledEvidence) = true := by
  rfl

example : CertificateReplay.replay?
    { certificate with reduction.halfTurns := 2 } = none := by rfl

example : CertificateReplay.replay?
    { certificate with reduction.halfTurns := 4 } = none := by rfl

example : CertificateReplay.replay?
    { certificate with reduction.negativeOutput := false } = none := by rfl

example : CertificateReplay.replay?
    { certificate with constant.upperNumerator := 17 } = none := by rfl

example : CertificateReplay.replay?
    { certificate with method := .taylorThree } = none := by rfl

/-- First ordinary theorem produced by the numerical provider pipeline. -/
theorem sinTenNegative : Real.sin 10 < 0 :=
  (CertificateReplay.replay? certificate).get (by rfl) |>.proof

/--
info: 'Hex.IntervalMathlib.SinTenConformance.sinTenNegative' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sinTenNegative

end Hex.IntervalMathlib.SinTenConformance
