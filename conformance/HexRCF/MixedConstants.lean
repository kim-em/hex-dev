/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.NamedConstants
public meta import HexRCF.NamedConstants
public import HexRCF.NormalizedInputs
public meta import HexRCF.NormalizedInputs
public meta import HexRCF.RealCoefficients
public meta import HexRCF.ProofEvidence

public section

namespace Hex.RCF.MixedConstants

open Hex RealCoefficients Lean Meta Qq
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

theorem pi_radical : ∀ x : ℝ, x ^ 2 + Real.pi - Real.sqrt 2 > 0 := by rcf

theorem pi_other_radical : ∀ x : ℝ, x ^ 2 + Real.pi - Real.sqrt 3 > 0 := by rcf

theorem exp_radical : ∀ x : ℝ,
    x ^ 2 + Real.exp 1 - (2 : ℝ) ^ (1 / 3 : ℝ) > 0 := by rcf

theorem exp_selected : ∀ x : ℝ,
    x ^ 2 + Real.exp 1 - CubeTwo.realAlgebraic.toReal > 0 := by rcf

theorem exp_normalized : ∀ x : ℝ,
    x ^ 2 + Real.exp 1 - NormalizedInputs.exposed.toReal > 0 := by rcf

@[expose] def selectedField : RealAlgebraicNumber :=
  Selected.field CubeTwo.polynomial CubeTwo.square
    (by decide) (by decide) (by rfl) (by decide) (by decide)
    CubeTwo.checked CubeTwo.squarefree (by decide)
    ((CubeTwo.realAlgebraic.toAlgebraic.toQAdjoin ^ 2 - 1) :
      QAdjoin CubeTwo.realAlgebraic.toAlgebraic)

theorem exp_field : ∀ x : ℝ,
    x ^ 2 + Real.exp 1 - selectedField.toReal > 0 := by rcf

@[expose] def negativeField : RealAlgebraicNumber :=
  Selected.field CubeTwo.polynomial CubeTwo.square
    (by decide) (by decide) (by rfl) (by decide) (by decide)
    CubeTwo.checked CubeTwo.squarefree (by decide)
    ((1 - CubeTwo.realAlgebraic.toAlgebraic.toQAdjoin ^ 2) :
      QAdjoin CubeTwo.realAlgebraic.toAlgebraic)

theorem pi_negative_field : ∀ x : ℝ,
    x ^ 2 + Real.pi + negativeField.toReal > 0 := by rcf

theorem pi_rational_root : ∀ x : ℝ,
    x ^ 2 + Real.pi - Real.sqrt (1 / 2) > 0 := by rcf

theorem pi_positive_divisor : ∀ x : ℝ,
    x ^ 2 + 1 / (Real.pi - Real.sqrt 2) > 0 := by rcf

theorem pi_negative_divisor : ∀ x : ℝ,
    x ^ 2 - 1 / (Real.sqrt 2 - Real.pi) > 0 := by rcf

theorem pi_cancelled : ∀ x : ℝ,
    x ^ 2 + Real.pi + 0 / (Real.pi - Real.sqrt 2) > 0 := by rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + Real.pi + 0 / (Real.sqrt 2 - Real.sqrt 2) > 0 := by rcf

/-- error: rcf: original closed divisor remains unresolved in supplied bounds -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + Real.pi + 0 / (NamedConstants.unknown - Real.sqrt 2) > 0 := by rcf

theorem false_sentence : ¬ (∀ x : ℝ, x ^ 2 + Real.sqrt 2 - Real.pi > 0) := by
  intro h
  have hzero := h 0
  have hs : Real.sqrt 2 ≤ 2 := by norm_num [Real.sqrt_le_iff]
  norm_num at hzero
  linarith [Real.pi_gt_three]

/-- error: rcf: algebraic enclosure needs a supported selected-field presentation -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + Real.pi - Real.sqrt (Real.sqrt 2) > 0 := by rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + Real.pi + 0 / (Real.sqrt 4 - 2) > 0 := by rcf

/-- error: rcf: original closed divisor remains unresolved in supplied bounds -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + Real.pi + 0 / ((2 : ℝ) ^ (1 / 3 : ℝ) - CubeTwo.realAlgebraic.toReal) > 0 := by rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x ∈ Set.Ioc (1 : ℝ) 0,
    x ^ 2 + Real.pi + 0 / (Real.sqrt 2 - Real.sqrt 2) > 0 := by rcf

private meta def refuses (action : MetaM α) : MetaM Unit := do
  let before ← getMCtx
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let failed ← tryCatchRuntimeEx (action *> pure false) (fun error => do
    if error.isRuntime || error.isInterrupt then throw error
    pure true)
  unless failed do throwError "expected mixed finite evidence rejection"
  unless (← getMCtx).mvarCounter == before.mvarCounter do
    throwError "failed mixed finite API leaked metavariables"
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "failed mixed finite API leaked proof auxiliaries"

run_elab do
  let before ← getMCtx
  let .ok value ← (Hex.RCF.Reify.recognizeCoefficient q(Real.sqrt 4)).run |
    throwError "rational radical was not recognized"
  unless value == 2 && (← getMCtx).mvarCounter == before.mvarCounter do
    throwError "rational scalar probe changed caller state or value"
  withLocalDeclD `alias q(ℝ) fun symbol => do
    withLocalDeclD `identity (← mkEq symbol q(Real.sqrt 2)) fun _ => do
      let before ← getMCtx
      let .error unsupported ← (Hex.RCF.Reify.recognizeCoefficient symbol).run |
        throwError "irrational alias was classified as rational"
      unless (← getMCtx).mvarCounter == before.mvarCounter &&
          !unsupported.closed.proof.hasMVar do
        throwError "unsupported scalar probe leaked metavariables"
      let _ ← Hex.RCF.checkProof `Hex.RCF.MixedConstants.alias
        (← mkEq unsupported.closed.value symbol) (← mkEqSymm unsupported.closed.proof)
  let prepared ← Finite.prepare q(∀ x : ℝ, x ^ 2 + Real.pi - Real.sqrt 3 > 0)
  let certificate ← Finite.build prepared
  let _ ← Finite.check prepared.source certificate
  unless prepared.registry.map Prod.fst == #[``NamedConstants.piRegistration] do
    throwError "mixed preparation included unused registrations"
  let some evidence := prepared.coefficients[0]? |
    throwError "mixed source lost its coefficient"
  refuses (Finite.check prepared.source {certificate with prepared := {prepared with
    coefficients := prepared.coefficients.set! 0 {evidence with
      bounds := Hex.OrderedFn.Oracle.Bounds.singleton 0}}})
  -- Validate earlier enclosures first, then reject a coherent literal/bounds
  -- forgery whose retained containment proof establishes different bounds.
  let last := prepared.coefficients.size - 1
  let some lastEvidence := prepared.coefficients[last]? |
    throwError "missing final enclosure for tamper test"
  let zero : Q(ℚ) := q(mkRat 0 1)
  let ordered ← mkDecideProof q($zero ≤ $zero)
  let forgedLiteral ← mkAppM ``Hex.OrderedFn.Oracle.Bounds.mk #[zero, zero, ordered]
  let forged := {lastEvidence with
    bounds := Hex.OrderedFn.Oracle.Bounds.singleton 0,
    literal := forgedLiteral}
  refuses (Finite.check prepared.source {certificate with prepared := {prepared with
    coefficients := prepared.coefficients.set! last forged}})
  -- Enclosure must finish before testing false-sentence proof reconstruction.
  let falseInput ← Finite.prepare q(∀ x : ℝ, x ^ 2 + Real.sqrt 2 - Real.pi > 0)
  refuses (Finite.build falseInput)
  let exactInput ← Finite.prepare q(∀ x : ℝ, x ^ 2 + Real.pi + Real.sqrt 4 - 2 > 0)
  let some exactEvidence := exactInput.coefficients.find? (fun e => e.source == q(Real.sqrt 4)) |
    throwError "perfect-square source lost its coefficient"
  unless exactEvidence.bounds.lower == 2 && exactEvidence.bounds.upper == 2 do
    throwError "perfect-square coefficient lost its exact rational bounds"
  let some exactName := exactEvidence.proof.getAppFn.constName? |
    throwError "perfect-square containment proof is not closed"
  if ← Hex.RCF.ProofEvidence.contains exactName
      (fun e => e.isConstOf ``AlgebraicBounds.contains_mkRat) then
    throwError "perfect-square source used approximate algebraic bounds"
  let before ← getMCtx
  let (_, proof) ← AlgebraicBounds.enclose q(Real.sqrt 3) (1 / 16)
  let proofName := proof.getAppFn.constName!
  let .thmInfo _ ← getConstInfo proofName |
    throwError "public algebraic enclosure did not kernel-check its proof"
  unless proofName != ``AlgebraicBounds.contains_mkRat &&
      ((← getEnv).getModuleIdxFor? proofName).isNone do
    throwError "public algebraic enclosure did not close a fresh kernel theorem"
  let _ ← Hex.RCF.checkProof `Hex.RCF.MixedConstants.publicEnclosure (← inferType proof) proof
  unless (← getMCtx).mvarCounter == before.mvarCounter do
    throwError "successful algebraic enclosure changed caller metavariables"
  let (_, rootProof) ← AlgebraicBounds.enclose q((3 : ℝ) ^ (1 / 3 : ℝ)) (1 / 16)
  let rootName := rootProof.getAppFn.constName!
  unless ← Hex.RCF.ProofEvidence.contains rootName
      (fun e => e.isConstOf ``RationalRoot.selected) do
    throwError "higher-root enclosure did not authenticate its selected embedding"
  let _ ← Hex.RCF.checkProof `Hex.RCF.MixedConstants.rootEnclosure
    (← inferType rootProof) rootProof
  refuses (AlgebraicBounds.enclose q(Real.sqrt (Real.sqrt 2)) (1 / 16))
  let shared ← Finite.prepare q(∀ x : ℝ, x ^ 2 + 1 / (Real.pi - Real.sqrt 2) > 0)
  let some guard := shared.guardBounds[0]? | throwError "missing shared guard bound"
  let some coefficient := shared.coefficients[0]? | throwError "missing inverse bound"
  let some guardName := guard.proof.getAppFn.constName? | throwError "guard proof is not closed"
  let some coefficientName := coefficient.proof.getAppFn.constName? |
    throwError "inverse proof is not closed"
  unless ← Hex.RCF.ProofEvidence.contains coefficientName (fun e => e.isConstOf guardName) do
    throwError "inverse coefficient did not reuse the checked guard enclosure"
  let shared ← Finite.prepare q(∀ x : ℝ,
    x / (Real.pi - Real.sqrt 2) = x / (Real.pi - Real.sqrt 2))
  let some guard := shared.guardBounds[0]? | throwError "missing normalized inverse guard"
  let some coefficient := shared.coefficients.find? (fun e => e.source.isAppOfArity ``Inv.inv 3) |
    throwError "variable division did not produce a closed inverse coefficient"
  let some guardName := guard.proof.getAppFn.constName? | throwError "inverse guard is not closed"
  let some coefficientName := coefficient.proof.getAppFn.constName? |
    throwError "normalized inverse proof is not closed"
  unless ← Hex.RCF.ProofEvidence.contains coefficientName (fun e => e.isConstOf guardName) do
    throwError "normalized inverse did not reuse its original guard enclosure"

end Hex.RCF.MixedConstants

open Hex.RCF.RealCoefficients

run_meta do
  for name in [`Hex.RCF.MixedConstants.pi_radical, `Hex.RCF.MixedConstants.pi_other_radical,
      `Hex.RCF.MixedConstants.exp_radical, `Hex.RCF.MixedConstants.pi_rational_root,
      `Hex.RCF.MixedConstants.exp_selected, `Hex.RCF.MixedConstants.exp_normalized,
      `Hex.RCF.MixedConstants.exp_field, `Hex.RCF.MixedConstants.pi_negative_field,
      `Hex.RCF.MixedConstants.pi_positive_divisor,
      `Hex.RCF.MixedConstants.pi_negative_divisor, `Hex.RCF.MixedConstants.pi_cancelled] do
    unless ← Hex.RCF.ProofEvidence.contains name
        (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound ||
          e.isConstOf ``Hex.RCF.RealCoefficients.Replay.check_sound) do
      throwError "mixed constant proof did not use algebraic literal replay"
    for forbidden in [``Hex.RCF.RealCoefficients.rootInterval,
        ``Hex.RealAlgebraicNumber.approxBall, ``Hex.RCF.RealCoefficients.Replay.build,
        ``Hex.RCF.RealCoefficients.FieldBuild.produceWithin] do
      if ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf forbidden) then
        throwError "mixed constant proof embedded algebraic production"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.MixedConstants.pi_rational_root
      (fun e => e.isConstOf ``RationalRoot.selected) do
    throwError "mixed rational-root proof did not use its checked embedding"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.MixedConstants.pi_other_radical
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.Replay.check_sound) do
    throwError "mixed sqrt3 proof did not use prepared finite replay"
  for (name, marker) in [(`Hex.RCF.MixedConstants.pi_radical, ``SquareTwo.valuation),
      (`Hex.RCF.MixedConstants.pi_positive_divisor, ``SquareTwo.valuation),
      (`Hex.RCF.MixedConstants.pi_negative_divisor, ``SquareTwo.valuation),
      (`Hex.RCF.MixedConstants.pi_cancelled, ``SquareTwo.valuation),
      (`Hex.RCF.MixedConstants.exp_radical, ``CubeTwo.valuation),
      (`Hex.RCF.MixedConstants.exp_selected, ``Selected.valuation),
      (`Hex.RCF.MixedConstants.exp_field, ``Selected.field_valuation),
      (`Hex.RCF.MixedConstants.pi_negative_field, ``Selected.field_valuation)] do
    unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf marker) do
      throwError "mixed proof used the wrong exact frontend"
    if ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf ``Replay.check_sound) then
      throwError "mixed exact frontend unexpectedly used prepared replay"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.MixedConstants.exp_normalized
      (fun e => e.isConstOf ``Replay.check_sound) do
    throwError "normalized leaf did not use prepared replay"

/-- info: 'Hex.RCF.MixedConstants.pi_radical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.pi_radical
/-- info: 'Hex.RCF.MixedConstants.pi_other_radical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.pi_other_radical
/-- info: 'Hex.RCF.MixedConstants.exp_radical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.exp_radical
/-- info: 'Hex.RCF.MixedConstants.exp_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.exp_selected
/-- info: 'Hex.RCF.MixedConstants.exp_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.exp_normalized
/-- info: 'Hex.RCF.MixedConstants.exp_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.exp_field
/-- info: 'Hex.RCF.MixedConstants.pi_negative_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.pi_negative_field
/-- info: 'Hex.RCF.MixedConstants.false_sentence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.false_sentence
/-- info: 'Hex.RCF.MixedConstants.pi_positive_divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.pi_positive_divisor
/-- info: 'Hex.RCF.MixedConstants.pi_negative_divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.pi_negative_divisor
/-- info: 'Hex.RCF.MixedConstants.pi_cancelled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.pi_cancelled

/-- info: 'Hex.RCF.MixedConstants.pi_rational_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.MixedConstants.pi_rational_root
