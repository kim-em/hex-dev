/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
public meta import HexRCF.ProofEvidence

public section
namespace Hex.RCF.RationalRoots
open Hex RealCoefficients Lean Meta Qq
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

theorem fraction : ∀ x : ℝ, x ^ 2 + Real.sqrt (1 / 2) > 0 := by rcf

theorem constructor : ∀ x : ℝ,
    x ^ 2 + Real.sqrt (RealAlgebraicNumber.ofRat (1 / 2)).toReal > 0 := by rcf

theorem square : ∀ x : ℝ, x ^ 2 - 2 * Real.sqrt (1 / 2) * x + 1 / 2 ≥ 0 := by rcf

theorem cube : ∀ x : ℝ, x ^ 2 + (3 : ℝ) ^ (1 / 3 : ℝ) * x + 1 > 0 := by rcf

theorem fourth : ∀ x : ℝ, x ^ 2 + (5 / 3 : ℝ) ^ (1 / 4 : ℝ) > 0 := by rcf

theorem inverse_exponent : ∀ x : ℝ, x ^ 2 + (5 : ℝ) ^ ((4 : ℝ)⁻¹) > 0 := by rcf

theorem direct_power : ∀ x : ℝ, x ^ 2 + Real.rpow (3 : ℝ) (1 / 5 : ℝ) > 0 := by rcf

theorem field_root : ∃ x : ℝ, x ^ 2 = Real.sqrt (1 / 2) ∧ 0 < x ∧ x < 1 := by rcf

theorem guarded_division : ∀ x : ℝ, x / Real.sqrt (1 / 2) = 2 * Real.sqrt (1 / 2) * x := by rcf

theorem cube_division : ∀ x : ℝ,
    x / (2 : ℝ) ^ (1 / 3 : ℝ) =
      ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 * x / 2 := by rcf

theorem alias_forward (a : ℝ) (h : a = (3 : ℝ) ^ (1 / 3 : ℝ)) :
    ∀ x : ℝ, x ^ 2 + a > 0 := by rcf

theorem alias_backward (a : ℝ) (h : (3 : ℝ) ^ (1 / 3 : ℝ) = a) :
    ∀ x : ℝ, x ^ 2 + a > 0 := by rcf

theorem alias_base (a : ℝ) (h : (1 / 2 : ℝ) = a) :
    ∀ x : ℝ, x ^ 2 + Real.sqrt a > 0 := by rcf

theorem half_open : ∀ x ∈ Set.Ioc (0 : ℝ) 1, x < Real.sqrt (1 / 2) → x ^ 2 < 1 / 2 := by rcf

theorem rational_square : ∀ x : ℝ,
    x ^ 2 + Real.sqrt 2 + Real.sqrt (9 / 4) > 0 := by rcf

theorem perfect_cube : ∀ x : ℝ,
    x ^ 2 + Real.sqrt 2 + (8 : ℝ) ^ (1 / 3 : ℝ) > 0 := by rcf

theorem shared_anchor : ∀ x : ℝ,
    x ^ 2 + Real.sqrt 2 - (4 : ℝ) ^ (1 / 4 : ℝ) = x ^ 2 := by rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + 0 / (Real.sqrt (1 / 2) - Real.sqrt (1 / 2)) ≥ 0 := by rcf

/-- error: rcf: symbolic or non-rational coefficient
  √(1 / 2 + 0 / (1 - 1)) -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + Real.sqrt (1 / 2 + 0 / (1 - 1)) > 0 := by rcf

/-- error: rcf: symbolic or non-rational coefficient
  3 ^ (1 / (3 + 0 / (1 - 1))) -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + (3 : ℝ) ^ (1 / (3 + 0 / (1 - 1)) : ℝ) > 0 := by rcf

theorem false_sentence : ¬ (∀ x : ℝ, x ^ 2 - Real.sqrt (1 / 2) > 0) := by
  intro h
  have hzero : -Real.sqrt (1 / 2) > 0 := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_sub] using h 0
  have hpositive : 0 < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- error: rcf: the universal sentence is false on the prepared cells -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 - Real.sqrt (1 / 2) > 0 := by rcf

private meta def refuses (action : MetaM α) : MetaM Unit := do
  let before ← getMCtx
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let failed ← tryCatchRuntimeEx (action *> pure false) fun error => do
    if error.isRuntime || error.isInterrupt then throw error
    pure true
  unless failed do throwError "expected rational-root proof refusal"
  unless (← getMCtx).mvarCounter == before.mvarCounter &&
      (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "rational-root proof refusal changed caller state"

run_elab do
  for (source, base, degree) in [(q(Real.sqrt (1 / 2)), (1 / 2 : Rat), 2),
      (q((3 : ℝ) ^ (1 / 3 : ℝ)), (3 : Rat), 3),
      (q((5 / 3 : ℝ) ^ (1 / 4 : ℝ)), (5 / 3 : Rat), 4)] do
    let .ok (some parameters) ← RationalRoot.parameters? source |
      throwError "positive rational-root source was not recognized"
    unless parameters.base == base && parameters.degree == degree do
      throwError "rational-root source was normalized incorrectly"
    let _ ← RationalRoot.identify source parameters
  let constructorSource := q(Real.sqrt (RealAlgebraicNumber.ofRat (1 / 2)).toReal)
  let .ok (some constructorParameters) ← RationalRoot.parameters? constructorSource |
    throwError "constructor-wrapped rational root was not recognized"
  let _ ← RationalRoot.identify constructorSource constructorParameters
  refuses (RationalRoot.identify q(Real.sqrt (1 / 2)) ⟨1 / 3, 2⟩)
  refuses (RationalRoot.identify q(Real.sqrt (1 / 2)) ⟨1 / 2, 3⟩)
  for (source, base, degree) in [(q(Real.sqrt (9 / 4)), (9 / 4 : Rat), 2),
      (q((8 : ℝ) ^ (1 / 3 : ℝ)), (8 : Rat), 3),
      (q((4 : ℝ) ^ (1 / 4 : ℝ)), (4 : Rat), 4)] do
    let (_, _, canonical) ← FieldRuntime.coefficient source
    unless canonical.toAlgebraic.p != RationalRoot.polynomial base degree do
      throwError "perfect-power control did not exercise a different canonical polynomial"
  let .ok none ← RationalRoot.parameters? q((-2 : ℝ) ^ (1 / 3 : ℝ)) |
    throwError "negative real-power branch was admitted"
  let .error (.unsupported _ _) ← RationalRoot.parameters? q((2 : ℝ) ^ (2 / 3 : ℝ)) |
    throwError "nonreciprocal root exponent was admitted"
  let .error (.budget _) ← RationalRoot.parameters? q((2 : ℝ) ^ (1 / 10000 : ℝ))
      {ring := {budget := {Hex.Reflect.Budget.default with exponent := 8}}} |
    throwError "shared root-degree budget was ignored"
  let large : Q(ℝ) := q(Real.sqrt (1 / (((2 : ℝ) ^ (64 : ℕ)) ^ (64 : ℕ))))
  let budgetGoal := q(∀ x : ℝ, x ^ 2 + Real.sqrt 3 + $large > 0)
  let .ok _ ← Reify.prepare budgetGoal |
    throwError "coefficient-size control did not reach leaf classification"
  let .error (.budget _) ← RationalRoot.parameters? large |
    throwError "coefficient-size control did not exhaust recognition"
  let beforeBudget ← getMCtx
  let budgetNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let .error (.budget _) ← Coefficients.prepare budgetGoal |
    throwError "coefficient preparation did not preserve structured recognition exhaustion"
  unless (← getMCtx).mvarCounter == beforeBudget.mvarCounter &&
      (← (← getEnv).getLocalConstantInfos).map (·.name) == budgetNames do
    throwError "structured recognition exhaustion changed caller state"
  for target in #[q(∀ x : ℝ,
      x ^ 2 + Real.sqrt 3 + $large + Real.sqrt (Real.sqrt 2) > 0),
      q(∀ x : ℝ, x ^ 2 + Real.sqrt (Real.sqrt 2) + $large + Real.sqrt 3 > 0)] do
    let .ok _ ← Reify.prepare target |
      throwError "unsupported-sibling control did not reach leaf classification"
    let before ← getMCtx
    let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let .error (.unsupported declined _) ← Coefficients.prepare target |
      throwError "recognition exhaustion preempted an unsupported sibling"
    unless declined == target do
      throwError "unsupported-sibling control did not decline at the environment boundary"
    unless (← getMCtx).mvarCounter == before.mvarCounter &&
        (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "deferred recognition refusal changed caller state"
  let largeBase : Q(ℝ) := q(1 / (((2 : ℝ) ^ (64 : ℕ)) ^ (64 : ℕ)))
  for unsupported in #[q(Real.pi), q(Real.sqrt 2)] do
    for root in #[q(Real.sqrt ($largeBase + $unsupported)),
        q(Real.sqrt ($unsupported + $largeBase))] do
      let root : Q(ℝ) ← pure root
      let .ok none ← RationalRoot.parameters? root |
        throwError "unsupported root-base syntax was hidden by arithmetic exhaustion"
      let target := q(∀ x : ℝ, x ^ 2 + Real.sqrt 3 + $root > 0)
      let .ok _ ← Reify.prepare target |
        throwError "unsupported root-base control did not reach leaf classification"
      let before ← getMCtx
      let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
      let .error (.unsupported declined _) ← Coefficients.prepare target |
        throwError "unsupported root-base operand order changed the refusal category"
      unless declined == target do
        throwError "unsupported root-base control did not decline at the environment boundary"
      unless (← getMCtx).mvarCounter == before.mvarCounter &&
          (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
        throwError "unsupported root-base refusal changed caller state"
  for root in #[q($largeBase ^ (Real.pi + $largeBase)),
      q($largeBase ^ ($largeBase + Real.pi))] do
    let .ok none ← RationalRoot.parameters? root |
      throwError "base exhaustion preempted an unsupported root exponent"
  let .error (.unsupported _ _) ← RationalRoot.parameters? q($largeBase ^ (2 / 3 : ℝ)) |
    throwError "base exhaustion preempted a nonreciprocal root exponent"
  let largeNatural : Q(ℝ) := q(Real.sqrt (((2 : ℝ) ^ (64 : ℕ)) ^ (64 : ℕ)))
  let naturalGoal := q(∀ x : ℝ, x ^ 2 + Real.sqrt 3 + $largeNatural > 0)
  let .ok _ ← Reify.prepare naturalGoal |
    throwError "natural-radicand control did not reach leaf classification"
  let .error (.budget _) ← RationalRoot.parameters? largeNatural |
    throwError "natural radicand bypassed the shared recognition budget"
  let beforeNatural ← getMCtx
  let naturalNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let .error (.budget _) ← Coefficients.prepare naturalGoal |
    throwError "natural-radicand preparation bypassed structured recognition exhaustion"
  unless (← getMCtx).mvarCounter == beforeNatural.mvarCounter &&
      (← (← getEnv).getLocalConstantInfos).map (·.name) == naturalNames do
    throwError "natural-radicand exhaustion changed caller state"
  let .ok division ← Reify.prepare q(∀ x : ℝ,
      x / (2 : ℝ) ^ (1 / 3 : ℝ) =
        ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 * x / 2) |
    throwError "higher-root division reached shared reification with a parameter denominator"
  unless division.coefficients.any (fun e => e.isAppOfArity ``Inv.inv 3) do
    throwError "higher-root divisor was not abstracted as a closed inverse"
  let .ok prepared ← Coefficients.prepare q(∀ x : ℝ, x ^ 2 + Real.sqrt (1 / 2) > 0) |
    throwError "rational-root coefficient environment was not prepared"
  let _ ← prepared.proveReplay
  let .ok falseInput ← Coefficients.prepare
      q(∀ x : ℝ, x ^ 2 - Real.sqrt (1 / 2) > 0) |
    throwError "false sentence failed before coefficient preparation"
  refuses falseInput.proveReplay
  let .error (.unsupported _ _) ← Coefficients.prepare
      q(∀ x : ℝ, x ^ 2 + Real.sqrt (Real.sqrt 2) > 0) |
    throwError "nested algebraic-base root unexpectedly admitted"

end Hex.RCF.RationalRoots

run_meta do
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.constructor
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "constructor root did not preserve its checked selected embedding"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.constructor
    (Lean.mkConst `Hex.RCF.RationalRoots.constructor)
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.alias_forward
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "root alias did not preserve its checked selected embedding"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.alias_forward
    (Lean.mkConst `Hex.RCF.RationalRoots.alias_forward)
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.alias_backward
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "root alias did not preserve its checked selected embedding"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.alias_backward
    (Lean.mkConst `Hex.RCF.RationalRoots.alias_backward)
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.alias_base
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "root alias did not preserve its checked selected embedding"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.alias_base
    (Lean.mkConst `Hex.RCF.RationalRoots.alias_base)
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.cube_division
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "guarded cube alias did not use common-field root authentication"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.cube_division
    (Lean.mkConst `Hex.RCF.RationalRoots.cube_division)
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.fraction
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "rational-root proof did not authenticate the new selected embedding"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.fraction
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound ||
        e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound) do
    throwError "rational-root proof did not use fixed-field literal replay"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.fraction (Lean.mkConst `Hex.RCF.RationalRoots.fraction)
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.square
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "rational-root proof did not authenticate the new selected embedding"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.square
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound ||
        e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound) do
    throwError "rational-root proof did not use fixed-field literal replay"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.square (Lean.mkConst `Hex.RCF.RationalRoots.square)
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.cube
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "rational-root proof did not authenticate the new selected embedding"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.cube
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound ||
        e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound) do
    throwError "rational-root proof did not use fixed-field literal replay"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.cube (Lean.mkConst `Hex.RCF.RationalRoots.cube)
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.fourth
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "rational-root proof did not authenticate the new selected embedding"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.fourth
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound ||
        e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound) do
    throwError "rational-root proof did not use fixed-field literal replay"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.fourth (Lean.mkConst `Hex.RCF.RationalRoots.fourth)
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.inverse_exponent
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "rational-root proof did not authenticate the new selected embedding"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.inverse_exponent
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound ||
        e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound) do
    throwError "rational-root proof did not use fixed-field literal replay"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.inverse_exponent (Lean.mkConst `Hex.RCF.RationalRoots.inverse_exponent)
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.direct_power
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "rational-root proof did not authenticate the new selected embedding"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.direct_power
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound ||
        e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound) do
    throwError "rational-root proof did not use fixed-field literal replay"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.direct_power (Lean.mkConst `Hex.RCF.RationalRoots.direct_power)
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.field_root
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "rational-root proof did not authenticate the new selected embedding"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.field_root
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound ||
        e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound) do
    throwError "rational-root proof did not use fixed-field literal replay"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.field_root (Lean.mkConst `Hex.RCF.RationalRoots.field_root)
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.guarded_division
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "rational-root proof did not authenticate the new selected embedding"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.guarded_division
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound ||
        e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound) do
    throwError "rational-root proof did not use fixed-field literal replay"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.guarded_division (Lean.mkConst `Hex.RCF.RationalRoots.guarded_division)
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.half_open
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
    throwError "rational-root proof did not authenticate the new selected embedding"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.RationalRoots.half_open
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound ||
        e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound) do
    throwError "rational-root proof did not use fixed-field literal replay"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.half_open (Lean.mkConst `Hex.RCF.RationalRoots.half_open)

/-- info: 'Hex.RCF.RationalRoots.fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.fraction

/-- info: 'Hex.RCF.RationalRoots.square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.square

/-- info: 'Hex.RCF.RationalRoots.cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.cube

/-- info: 'Hex.RCF.RationalRoots.fourth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.fourth

/-- info: 'Hex.RCF.RationalRoots.inverse_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.inverse_exponent

/-- info: 'Hex.RCF.RationalRoots.direct_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.direct_power

/-- info: 'Hex.RCF.RationalRoots.field_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.field_root

/-- info: 'Hex.RCF.RationalRoots.guarded_division' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.guarded_division

/-- info: 'Hex.RCF.RationalRoots.half_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.half_open

/-- info: 'Hex.RCF.RationalRoots.false_sentence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.false_sentence

/-- info: 'Hex.RCF.RationalRoots.cube_division' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.cube_division

/-- info: 'Hex.RCF.RationalRoots.alias_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.alias_forward

/-- info: 'Hex.RCF.RationalRoots.alias_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.alias_backward

/-- info: 'Hex.RCF.RationalRoots.alias_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.alias_base

/-- info: 'Hex.RCF.RationalRoots.constructor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.constructor

run_meta do
  for name in [`Hex.RCF.RationalRoots.rational_square, `Hex.RCF.RationalRoots.perfect_cube,
      `Hex.RCF.RationalRoots.shared_anchor] do
    unless ← Hex.RCF.ProofEvidence.contains name
        (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
      throwError "perfect-power control {name} did not authenticate the original root alias"
    Hex.RCF.checkAxioms name (Lean.mkConst name)

/-- info: 'Hex.RCF.RationalRoots.rational_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.rational_square

/-- info: 'Hex.RCF.RationalRoots.perfect_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.perfect_cube

/-- info: 'Hex.RCF.RationalRoots.shared_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.shared_anchor
