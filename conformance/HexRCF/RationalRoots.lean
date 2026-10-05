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

theorem inverse_base : ∀ x : ℝ, x ^ 2 + Real.sqrt ((2 : ℝ)⁻¹) > 0 := by rcf

theorem inverse_natural : ∀ x : ℝ,
    x ^ 2 + Real.sqrt (4 * (2 : ℝ)⁻¹) + Real.sqrt (8 * (2 : ℝ)⁻¹ + 1) > 0 := by rcf

theorem constructor_exponent : ∀ x : ℝ,
    x ^ 2 + (3 : ℝ) ^ (RealAlgebraicNumber.ofRat (1 / 3)).toReal > 0 := by rcf

theorem type_alias : ∀ x : ℝ,
    x ^ 2 + @HPow.hPow ℝ (id ℝ) ℝ (inferInstance : HPow ℝ ℝ ℝ)
      (5 / 3) (1 / 4 : ℝ) > 0 := by rcf

run_elab do
  let config : Hex.RealFormula.Reify.Config :=
    {ring := {budget := {Hex.Reflect.Budget.default with coefficientBits := 8}}}
  let degree (source : Expr) := ((Coefficients.rootDegree source).run
    {config, budget := .ofBudget config.ring.budget}).run
  let .ok (3, _) ← degree q((1 / 3 : ℝ)) |
    throwError "bounded reciprocal-degree recognition refused an ordinary exponent"
  -- The largest literal calculation is only 2^64, even on a regressed path.
  let large : Q(ℝ) := q(((2 : ℝ) ^ (8 : ℕ)) ^ (8 : ℕ))
  let exponent : Q(ℝ) := q(($large - $large + 1) / 3)
  let .error (.budget exhausted) ← degree exponent |
    throwError "cancelled exponent numerator bypassed coefficient admission"
  unless exhausted.dimension == .coefficientBits do
    throwError "exponent numerator used the wrong resource dimension"
  let .error (.budget exhausted) ← RationalRoot.parameters? q((2 : ℝ) ^ $exponent) config |
    throwError "root parameter admission bypassed the exponent numerator bound"
  unless exhausted.dimension == .coefficientBits do
    throwError "root parameter admission used the wrong resource dimension"
  let zeroPower : Q(ℝ) := q($large ^ (0 : ℕ))
  let .error (.budget exhausted) ← degree q($zeroPower / 3) |
    throwError "zero exponent hid an oversized reciprocal-degree numerator"
  unless exhausted.dimension == .coefficientBits do
    throwError "zero-power admission used the wrong resource dimension"
  let .error (.budget _) ← RationalRoot.parameters? q(Real.sqrt $zeroPower) config |
    throwError "zero exponent hid an oversized root base"
  let beforeFrontend ← getMCtx
  let frontendNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
  for target in #[q(∀ x : ℝ, x ^ 2 + (2 : ℝ) ^ ($zeroPower / 3) > 0),
      q(∀ x ∈ Set.Ioc ($zeroPower / 2) (1 : ℝ), x ^ 2 ≥ 0),
      q(∀ x : ℝ, x ^ 2 + (RealAlgebraicNumber.ofRat 1).toReal +
        Real.sqrt (1 / $large) > 0),
      q(∀ x : ℝ, x ^ 2 + (RealAlgebraicNumber.ofRat 1).toReal +
        Real.sqrt (1 / $zeroPower) > 0)] do
    let .error (.budget exhausted) ← Reify.prepare target config |
      throwError "source preparation bypassed an intermediate numerator bound"
    unless exhausted.dimension == .coefficientBits do
      throwError "source preparation used the wrong resource dimension"
    unless (← getMCtx).mvarCounter == beforeFrontend.mvarCounter &&
        (← (← getEnv).getLocalConstantInfos).map (·.name) == frontendNames do
      throwError "source budget refusal changed caller state"
  let mut small : Q(ℝ) := q(1)
  for _ in [:32] do small := q($small ^ (0 : ℕ))
  let .ok (3, _) ← degree q($small / 3) |
    throwError "retaining zero-power bases inflated bounded unit arithmetic"
  let .ok (literal, _) ← ((Hex.RealFormula.Reify.arithmetic #[] q((1024 : ℝ))).run
      {config := {}, budget := .ofBudget Hex.Reflect.Budget.default}).run |
    throwError "literal numerator setup failed"
  let .error (.budget _) ← ((Coefficients.boundNumerator literal.numerator).run
      {config, budget := .ofBudget config.ring.budget}).run |
    throwError "shared reification hid an integer-cast literal as an opaque atom"
  let .error (.unsupported _ _) ← degree q((0 / (3 - 3) + 1 / 3 : ℝ)) |
    throwError "cancelled zero divisor survived exponent admission"
  let .error (.unsupported _ _) ← degree q((Real.sin 0 + 1 / 3 : ℝ)) |
    throwError "unsupported exponent was hidden by coefficient admission"

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

/-- error: rcf: budget exhausted in dimension literal exponent: limit 2, consumed 2, requested 4 (common-field degree; see rcf.algebraic.commonDegree) -/
#guard_msgs (whitespace := lax) in
set_option rcf.algebraic.commonDegree 2 in
example : ∀ x : ℝ, x ^ 2 + Real.sqrt 2 + Real.sqrt 3 > 0 := by rcf

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
  let .ok (some inverseParameters) ← RationalRoot.parameters? q(Real.sqrt ((2 : ℝ)⁻¹)) |
    throwError "inverse-base notation was not admitted"
  unless inverseParameters.base == 1 / 2 && inverseParameters.degree == 2 do
    throwError "inverse-base parameters differ from their rational interpretation"
  let wrapped := Expr.mdata {} q(Real.sqrt ((2 : ℝ)⁻¹))
  unless RationalRoot.isNotation wrapped && (← RationalRoot.hasSyntax wrapped) do
    throwError "metadata hid root admission"
  let .ok (some wrappedParameters) ← RationalRoot.parameters? wrapped |
    throwError "metadata hid root parameters"
  let _ ← RationalRoot.identify wrapped wrappedParameters
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
  let .error (.budget _) ← RationalRoot.parameters?
      q(Real.sqrt ($largeBase + 0 / (1 - 1))) |
    throwError "bounded arithmetic did not exhaust before an unevaluated zero divisor"
  let .error (.unsupported _ _) ← RationalRoot.parameters?
      q(Real.sqrt (0 / (1 - 1) + $largeBase)) |
    throwError "evaluated zero divisor was admitted by rational-root recognition"
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
  let inverseLarge := q(Real.sqrt ((2 : ℝ)⁻¹ * 2 *
    (((2 : ℝ) ^ (64 : ℕ)) ^ (64 : ℕ))))
  let .error (.budget _) ← RationalRoot.parameters? inverseLarge |
    throwError "inverse-containing radicand bypassed bounded normalization"
  let wrappedLarge := Expr.mdata {} inverseLarge
  let .error (.budget _) ← RationalRoot.parameters? wrappedLarge |
    throwError "metadata hid inverse-containing radicand exhaustion"
  refuses (AlgebraicBounds.enclose wrappedLarge (1 / 4))
  let powerLarge : Q(ℝ) := q((((2 : ℝ) ^ (64 : ℕ)) ^ (64 : ℕ)) ^ (1 / 2 : ℝ))
  let powerArgs := powerLarge.getAppArgs
  let wrappedType := mkAppN powerLarge.getAppFn
    (powerArgs.set! 1 (.mdata {} powerArgs[1]!))
  let _ ← Hex.RCF.checkProof `Hex.RCF.RationalRoots.typeMetadata
    (← mkEq wrappedType wrappedType) (← mkEqRefl wrappedType)
  unless RationalRoot.isNotation wrappedType do
    throwError "type-argument metadata hid real root notation"
  let .error (.budget _) ← RationalRoot.parameters? wrappedType |
    throwError "type-argument metadata hid root admission exhaustion"
  refuses (AlgebraicBounds.enclose wrappedType (1 / 4))
  let aliasType : Q(Type) := q(id ℝ)
  let aliasPower := mkAppN powerLarge.getAppFn (powerArgs.set! 1 aliasType)
  let _ ← Hex.RCF.checkProof `Hex.RCF.RationalRoots.typeAlias
    (← mkEq aliasPower aliasPower) (← mkEqRefl aliasPower)
  unless ← RationalRoot.isRealPower aliasPower do
    throwError "definitionally real exponent type bypassed typed admission"
  let .error (.budget _) ← RationalRoot.parameters? aliasPower |
    throwError "definitionally real power bypassed recognition exhaustion"
  refuses (AlgebraicBounds.enclose aliasPower (1 / 4))
  let aliasedExponent := mkApp2 (mkConst ``id [.succ .zero]) aliasType q((1 / 2 : ℝ))
  let inferred ← inferType aliasedExponent
  if inferred.isConstOf ``Real then
    throwError "inferred-type alias fixture unexpectedly became syntactic Real"
  let inferredAlias := mkAppN powerLarge.getAppFn
    ((powerArgs.set! 1 aliasType).set! 5 aliasedExponent)
  let _ ← Hex.RCF.checkProof `Hex.RCF.RationalRoots.inferredTypeAlias
    (← mkEq inferredAlias inferredAlias) (← mkEqRefl inferredAlias)
  let beforeAlias ← getMCtx
  unless ← RationalRoot.isRealPower inferredAlias do
    throwError "definitionally real inferred exponent type bypassed admission"
  unless (← getMCtx).mvarCounter == beforeAlias.mvarCounter do
    throwError "typed power detection changed caller metavariable state"
  if ← RationalRoot.isRealPower q((2 : ℝ) ^ (3 : ℕ)) then
    throwError "typed real-power admission classified a natural power as a root"
  let combined := q(∀ x : ℝ, x ^ 2 + Real.sqrt 2 + Real.sqrt 3 > 0)
  let beforeCombined ← getMCtx
  let combinedNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let .error (.budget exhausted) ← withOptions (CommonTactic.rcf.algebraic.commonDegree.set · 2)
      (Coefficients.prepare combined) |
    throwError "combined generator degree was not bounded"
  unless exhausted.dimension == .exponent && exhausted.limit == 2 &&
      exhausted.consumed == 2 && exhausted.requested == 4 do
    throwError "combined generator degree report lost its exact admission bounds"
  unless (← getMCtx).mvarCounter == beforeCombined.mvarCounter &&
      (← (← getEnv).getLocalConstantInfos).map (·.name) == combinedNames do
    throwError "combined degree exhaustion changed caller state"
  let .ok _ ← withOptions (CommonTactic.rcf.algebraic.commonDegree.set · 2) <|
      Coefficients.prepare q(∀ x : ℝ,
        x ^ 2 + Real.sqrt 2 - (4 : ℝ) ^ (1 / 4 : ℝ) = x ^ 2) |
    throwError "repeated selected anchor was charged twice"
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
  for name in [`Hex.RCF.RationalRoots.inverse_base,
      `Hex.RCF.RationalRoots.inverse_natural, `Hex.RCF.RationalRoots.constructor_exponent] do
    Hex.RCF.checkAxioms name (Lean.mkConst name)
  for name in [`Hex.RCF.RationalRoots.inverse_base,
      `Hex.RCF.RationalRoots.constructor_exponent, `Hex.RCF.RationalRoots.type_alias] do
    unless ← Hex.RCF.ProofEvidence.contains name
        (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.RationalRoot.selected) do
      throwError "inverse/constructor root proof did not authenticate the selected embedding"
  Hex.RCF.checkAxioms `Hex.RCF.RationalRoots.type_alias (Lean.mkConst `Hex.RCF.RationalRoots.type_alias)

/-- info: 'Hex.RCF.RationalRoots.type_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.type_alias

/-- info: 'Hex.RCF.RationalRoots.inverse_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.inverse_base

/-- info: 'Hex.RCF.RationalRoots.inverse_natural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.inverse_natural

/-- info: 'Hex.RCF.RationalRoots.constructor_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RationalRoots.constructor_exponent

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
