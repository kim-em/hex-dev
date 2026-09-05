/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.SinTen
public import HexInterval.Experiment.SemanticReplay
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# A Machin-derived range reduction for `Real.sin 10`

This proof-side experiment keeps constant replay, integer range reduction,
local sine enclosure, and final reconstruction as distinct steps. Candidate
data is executable and untrusted; every accepted step returns ordinary kernel
evidence.
-/

namespace Hex.IntervalMathlib.Experiment.SinTen

open Set
open Hex.Interval.Experiment.SemanticReplay
open Hex.Interval.Experiment.SinTen

noncomputable def candidateValue (numerator denominator : Nat) : ℝ :=
  numerator / denominator

namespace MachinReplay

/-- The first two alternating terms give a strict lower bound on arctangent.
This calculus proof is provider-owned rather than a fact known to the interval
scheduler. -/
theorem subCube_lt_arctan {x : ℝ} (positive : 0 < x) :
    x - x ^ 3 / 3 < Real.arctan x := by
  let f (t : ℝ) := Real.arctan t - (t - t ^ 3 / 3)
  have derivative (t : ℝ) :
      deriv f t = 1 / (1 + t ^ 2) - 1 + t ^ 2 := by
    simp (disch := first | exact Real.differentiableAt_arctan _ | fun_prop)
      [f, Real.deriv_arctan]
    ring
  have monotone : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    intro t ht
    rw [interior_Ici, mem_Ioi] at ht
    rw [derivative]
    have denominator : 0 < 1 + t ^ 2 := by positivity
    rw [show 1 / (1 + t ^ 2) - 1 + t ^ 2 = t ^ 4 / (1 + t ^ 2) by
      field_simp
      ring]
    exact div_pos (pow_pos ht 4) denominator
  have compared : f 0 < f x := monotone (by simp) positive.le positive
  simpa [f] using compared

/-- Arctangent lies strictly below its positive argument. -/
theorem arctan_lt {x : ℝ} (positive : 0 < x) : Real.arctan x < x := by
  have range := Real.arctan_mem_Ioo x
  have anglePositive : 0 < Real.arctan x := Real.arctan_pos.mpr positive
  simpa only [Real.tan_arctan] using Real.lt_tan anglePositive range.2

/-- A coarse Machin-derived enclosure sufficient to authenticate the
reduction integer for this canary. -/
theorem pi_bounds : (3 : ℝ) < Real.pi ∧ Real.pi < 16 / 5 := by
  have identity := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have lowerFive :
      (1 / 5 : ℝ) - (1 / 5 : ℝ) ^ 3 / 3 < Real.arctan (5 : ℝ)⁻¹ := by
    convert subCube_lt_arctan (x := (1 / 5 : ℝ)) (by norm_num) using 1
    all_goals norm_num
  have upperFive : Real.arctan (5 : ℝ)⁻¹ < (1 / 5 : ℝ) := by
    convert arctan_lt (x := (1 / 5 : ℝ)) (by norm_num) using 1
    all_goals norm_num
  have positiveTwoThirtyNine : 0 < Real.arctan (239 : ℝ)⁻¹ :=
    Real.arctan_pos.mpr (by positivity)
  have upperTwoThirtyNine :
      Real.arctan (239 : ℝ)⁻¹ < (1 / 239 : ℝ) := by
    convert arctan_lt (x := (1 / 239 : ℝ)) (by norm_num) using 1
    all_goals norm_num
  constructor <;> nlinarith

/-- The mathematical claim is indexed by the untrusted endpoint data. -/
noncomputable def Claim (candidate : ConstantCandidate) : Prop :=
  candidateValue candidate.lowerNumerator candidate.lowerDenominator < Real.pi ∧
    Real.pi < candidateValue candidate.upperNumerator candidate.upperDenominator

/-- Exact endpoint acceptance is the load-bearing authentication step. -/
def replay? (candidate : ConstantCandidate) : Option (Evidence (Claim candidate)) :=
  if accepted : Machin.accepts candidate then
    have equal : candidate = Machin.candidate := by
      simpa [Machin.accepts] using accepted
    some
      { proof := by
          subst candidate
          simpa [Claim, candidateValue, Machin.candidate] using pi_bounds }
  else none

end MachinReplay

namespace LocalReplay

/-- The complete interface consumed by the local sine theorem. -/
structure Core (x : ℝ) : Prop where
  positive : 0 < x
  belowPi : x < Real.pi

def Claim (x : ℝ) : Prop := 0 < Real.sin x

/-- Local replay consumes only core-domain facts, not a range-reduction
certificate or reconstruction theorem. -/
def replay? (method : LocalMethod) {x : ℝ} (core : Evidence (Core x)) :
    Option (Evidence (Claim x)) :=
  if accepted : Local.accepts method then
    have equal : method = .positiveCore := by
      simpa [Local.accepts] using accepted
    some
      { proof := by
          subst method
          exact Real.sin_pos_of_pos_of_lt_pi core.proof.positive core.proof.belowPi }
  else none

end LocalReplay

namespace ReductionReplay

noncomputable def residual (candidate : ReductionCandidate) : ℝ :=
  10 - candidate.halfTurns * Real.pi

/-- Apply the quadrant sign selected by the candidate. -/
def signed (negative : Bool) (value : ℝ) : ℝ :=
  if negative then -value else value

structure Result (candidate : ReductionCandidate) : Prop where
  accepted : Reduction.accepts candidate = true
  core : LocalReplay.Core (residual candidate)
  reconstruct :
    Real.sin (residual candidate) = signed candidate.negativeOutput (Real.sin 10)

/-- Reduction replay accepts any proved constant enclosure whose numeric
endpoints are bounded and strong enough to authenticate half-turn `3`. -/
def replay? (constantCandidate : ConstantCandidate)
    (candidate : ReductionCandidate)
    (constant : Evidence (MachinReplay.Claim constantCandidate)) :
    Option (Evidence (Result candidate)) :=
  if constantAdequate : Reduction.adequate constantCandidate then
    if reductionAccepted : Reduction.accepts candidate then
      have reductionEqual : candidate = Reduction.candidate := by
        simpa [Reduction.accepts] using reductionAccepted
      some
        { proof := by
            subst candidate
            simp only [Reduction.adequate, decide_eq_true_eq] at constantAdequate
            rcases constantAdequate with
              ⟨_, _, _, _, lowerNonzero, upperNonzero, upperCross, lowerCross⟩
            have lowerPositive : (0 : ℝ) < constantCandidate.lowerDenominator := by
              exact_mod_cast Nat.pos_of_ne_zero lowerNonzero
            have upperPositive : (0 : ℝ) < constantCandidate.upperDenominator := by
              exact_mod_cast Nat.pos_of_ne_zero upperNonzero
            have upperCrossReal :
                (3 : ℝ) * constantCandidate.upperNumerator ≤
                  10 * constantCandidate.upperDenominator := by
              exact_mod_cast upperCross
            have lowerCrossReal :
                (10 : ℝ) * constantCandidate.lowerDenominator ≤
                  4 * constantCandidate.lowerNumerator := by
              exact_mod_cast lowerCross
            have upperAdequate :
                3 * candidateValue constantCandidate.upperNumerator
                    constantCandidate.upperDenominator ≤ 10 := by
              calc
                3 * candidateValue constantCandidate.upperNumerator
                    constantCandidate.upperDenominator =
                    (3 * constantCandidate.upperNumerator : ℝ) /
                      constantCandidate.upperDenominator := by
                      simp only [candidateValue]
                      ring
                _ ≤ 10 := (div_le_iff₀ upperPositive).2 (by
                  simpa only [mul_comm] using upperCrossReal)
            have lowerAdequate :
                10 ≤ 4 * candidateValue constantCandidate.lowerNumerator
                    constantCandidate.lowerDenominator := by
              calc
                10 ≤ (4 * constantCandidate.lowerNumerator : ℝ) /
                    constantCandidate.lowerDenominator :=
                  (le_div_iff₀ lowerPositive).2 (by
                    simpa only [mul_comm] using lowerCrossReal)
                _ = 4 * candidateValue constantCandidate.lowerNumerator
                    constantCandidate.lowerDenominator := by
                      simp only [candidateValue]
                      ring
            rcases constant.proof with ⟨piLower, piUpper⟩
            have threePi : 3 * Real.pi < 10 :=
              lt_of_lt_of_le (mul_lt_mul_of_pos_left piUpper (by norm_num))
                upperAdequate
            have fourPi : 10 < 4 * Real.pi :=
              lt_of_le_of_lt lowerAdequate
                (mul_lt_mul_of_pos_left piLower (by norm_num))
            refine ⟨by simp [Reduction.accepts], ⟨?_, ?_⟩, ?_⟩
            · simp only [residual, Reduction.candidate]
              norm_num at threePi ⊢
              linarith
            · simp only [residual, Reduction.candidate]
              norm_num at fourPi ⊢
              linarith
            · convert (Real.sin_sub_nat_mul_pi 10 3) using 1 <;>
                norm_num [residual, signed, Reduction.candidate] }
    else none
  else none

end ReductionReplay

namespace CertificateReplay

/-- Fixed pipeline orchestration for this canary. The individual stages own
their acceptance tests and mathematical theorems. -/
noncomputable def replay? (certificate : Certificate) :
    Option (Evidence (Real.sin 10 < 0)) := do
  let constant ← MachinReplay.replay? certificate.constant
  let reduction ← ReductionReplay.replay? certificate.constant
    certificate.reduction constant
  let localEvidence ← LocalReplay.replay? certificate.method
    { proof := reduction.proof.core }
  some
    { proof := by
        have reductionEqual : certificate.reduction = Reduction.candidate := by
          simpa [Reduction.accepts] using reduction.proof.accepted
        have positive := localEvidence.proof
        have reconstructed := reduction.proof.reconstruct
        rw [reductionEqual] at positive reconstructed
        simp only [Reduction.candidate, LocalReplay.Claim] at positive
        simp only [Reduction.candidate, ReductionReplay.signed, ite_true] at reconstructed
        linarith }

end CertificateReplay

end Hex.IntervalMathlib.Experiment.SinTen

end
