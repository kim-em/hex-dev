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
namespace Hex.RCF.AlgebraicRoots
open Hex RealCoefficients Lean Meta Qq
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem square : ∀ x : ℝ,
    x ^ 2 - 2 * Real.sqrt (Real.sqrt 2) * x + Real.sqrt 2 ≥ 0 := by
  rcf

theorem shifted : ∃ x : ℝ, x = Real.sqrt (3 + Real.sqrt 2) ∧ 2 < x ∧ x < 3 := by
  rcf

theorem cubic : ∀ x : ℝ, x ^ 2 + (3 + Real.sqrt 2) ^ (1 / 3 : ℝ) > 0 := by
  rcf

theorem cancelled : ∀ x : ℝ,
    x ^ 2 + Real.sqrt (Real.sqrt 2 - Real.sqrt 2) ≥ 0 := by
  rcf

theorem guarded : ∀ x : ℝ, x ^ 2 + Real.sqrt (1 / (4 + Real.sqrt 2)) > 0 := by
  rcf

theorem negativeDegreeOne : ∀ x : ℝ, x ^ 2 > (-Real.sqrt 2) ^ (1 / 1 : ℝ) := by
  rcf

theorem deeper : ∃ x : ℝ, x = Real.sqrt (Real.sqrt (Real.sqrt 2)) ∧ 1 < x ∧ x < 2 := by
  rcf

theorem explicitPower : ∀ x : ℝ,
    x ^ 2 + Real.rpow (3 + Real.sqrt 2) (1 / 3) > 0 := by rcf

theorem sharedAnchor : ∀ x : ℝ,
    x ^ 2 + Real.sqrt (Real.sqrt 2) - (2 : ℝ) ^ (1 / 4 : ℝ) = x ^ 2 := by rcf

theorem rationalBase : ∀ x : ℝ, x ^ 2 + Real.sqrt (Real.sqrt 4 + 1) > 0 := by rcf

theorem selectedBase : ∀ x : ℝ,
    x ^ 2 + Real.sqrt CubeTwo.realAlgebraic.toReal > 0 := by rcf

theorem sharedBase : ∀ x : ℝ,
    x ^ 2 + Real.sqrt (Real.sqrt 4 + 1) +
      (Real.sqrt 4 + 1) ^ (1 / 1 : ℝ) > 0 := by rcf

theorem sharedNested : ∀ x : ℝ,
    x ^ 2 + Real.sqrt (Real.sqrt (Real.sqrt 4 + 1)) +
      (Real.sqrt 4 + 1) ^ (1 / 1 : ℝ) > 0 := by rcf

run_elab do
  for name in #[`Hex.RCF.AlgebraicRoots.square,
      `Hex.RCF.AlgebraicRoots.shifted,
      `Hex.RCF.AlgebraicRoots.cubic,
      `Hex.RCF.AlgebraicRoots.cancelled,
      `Hex.RCF.AlgebraicRoots.guarded,
      `Hex.RCF.AlgebraicRoots.deeper,
      `Hex.RCF.AlgebraicRoots.explicitPower,
      `Hex.RCF.AlgebraicRoots.sharedAnchor,
      `Hex.RCF.AlgebraicRoots.rationalBase,
      `Hex.RCF.AlgebraicRoots.selectedBase,
      `Hex.RCF.AlgebraicRoots.sharedBase,
      `Hex.RCF.AlgebraicRoots.sharedNested,
      `Hex.RCF.AlgebraicRoots.negativeDegreeOne] do
    let markers := #[``CommonPresentation.checkEntry_sound_of_selected,
      ``CommonPresentation.checkPolynomials_sound]
    let markers := if name == `Hex.RCF.AlgebraicRoots.negativeDegreeOne then markers
      else markers.push ``CommonPresentation.checkRoot_sound
    for marker in markers do
      unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf marker) do
        throwError "tactic proof omitted source authentication {marker}"
    if ← Hex.RCF.ProofEvidence.contains name (fun e =>
        e.getAppFn.constName?.any (fun n =>
          ((`Hex.RCF.RealCoefficients.FieldBuild).isPrefixOf n &&
            !(`Hex.RCF.RealCoefficients.FieldBuild.Result).isPrefixOf n) ||
          (`Hex.RCF.RealCoefficients.FieldRuntime).isPrefixOf n ||
          #[``Coefficients.root, ``LiteralSign.Table.build,
            ``Replay.build, ``Replay.buildTotal, ``Field.prepareSign,
            ``Sturm.queryPrepared, ``Sturm.certifyPrepared,
            ``RealAlgebraicNumber.ofAlgebraic?, ``PolyQuot.toAlgebraicNumber,
            ``AlgebraicRoot.identify,
            ``QAdjoin.common, ``RealAlgebraicNumber.approxBall,
            ``HexBerlekampZassenhaus.FactorTactic.searchWitness,
            ``Hex.certifyIrreducible?, ``Hex.QuadraticNormCertificate.certify?].contains n)) then
      throwError "tactic proof transitively includes native production"
    unless ← Hex.RCF.ProofEvidence.contains name (fun e =>
        e.isConstOf ``FieldBuild.Result.checkForall_sound ||
        e.isConstOf ``FieldBuild.Result.checkExists_sound) do
      throwError "tactic proof omitted ordinary cell replay soundness"

/-- info: 'Hex.RCF.AlgebraicRoots.square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms square
/-- info: 'Hex.RCF.AlgebraicRoots.shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shifted
/-- info: 'Hex.RCF.AlgebraicRoots.cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic
/-- info: 'Hex.RCF.AlgebraicRoots.cancelled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cancelled
/-- info: 'Hex.RCF.AlgebraicRoots.guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guarded
/-- info: 'Hex.RCF.AlgebraicRoots.negativeDegreeOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negativeDegreeOne
/-- info: 'Hex.RCF.AlgebraicRoots.deeper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deeper

/-- info: 'Hex.RCF.AlgebraicRoots.explicitPower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms explicitPower
/-- info: 'Hex.RCF.AlgebraicRoots.sharedAnchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sharedAnchor

/-- info: 'Hex.RCF.AlgebraicRoots.rationalBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rationalBase
/-- info: 'Hex.RCF.AlgebraicRoots.selectedBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selectedBase

/-- info: 'Hex.RCF.AlgebraicRoots.sharedBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sharedBase
/-- info: 'Hex.RCF.AlgebraicRoots.sharedNested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sharedNested

run_elab do
  let cache ← IO.mkRef ({} : ExprMap AlgebraicRoot.Identity)
  let calls ← IO.mkRef 0
  let prepareBase target := do
    calls.modify (· + 1)
    Coefficients.prepare target
  let limit := CommonTactic.rcf.algebraic.commonDegree.get (← getOptions)
  let .ok _ ← (AlgebraicRoot.identify q(Real.sqrt (3 + Real.sqrt 2))
      q(3 + Real.sqrt 2) 2 prepareBase limit (some cache)).run |
    throwError "square-root cache fixture failed"
  let .ok _ ← (AlgebraicRoot.identify q((3 + Real.sqrt 2) ^ (1 / 3 : ℝ))
      q(3 + Real.sqrt 2) 3 prepareBase limit (some cache)).run |
    throwError "cube-root cache fixture failed"
  unless (← calls.get) == 1 do throwError "shared base repeated authentication"
  let .error (.budget exhausted) ← (AlgebraicRoot.identify
      q((3 + Real.sqrt 2) ^ (1 / 3 : ℝ)) q(3 + Real.sqrt 2) 3
      prepareBase 4 (some cache)).run |
    throwError "cached base bypassed degree admission"
  unless exhausted.consumed == 2 && exhausted.requested == 6 &&
      (← calls.get) == 1 do throwError "cached degree admission was incorrect"
  let .error (.budget early) ← (AlgebraicRoot.identify
      q((3 + Real.sqrt 2) ^ (1 / 5 : ℝ)) q(3 + Real.sqrt 2) 5
      prepareBase 4).run |
    throwError "oversized root was not refused before base preparation"
  unless early.consumed == 0 && early.requested == 5 &&
      (← calls.get) == 1 do throwError "early degree refusal ran base preparation"
  let base : Expr ← pure q((3 : ℝ) + Real.sqrt 2)
  let some entry := (← cache.get)[base]? |
    throwError "shared base was not cached"
  cache.modify (·.insert base
    {entry with proof := mkConst `Hex.RCF.AlgebraicRoots.missingBaseProof})
  let before ← getMCtx
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let .error (.internal "cached base proof is unavailable") ←
      (AlgebraicRoot.identify q(Real.sqrt (3 + Real.sqrt 2))
        q(3 + Real.sqrt 2) 2 prepareBase limit (some cache)).run |
    throwError "cache accepted a missing proof declaration"
  unless (← calls.get) == 1 && (← getMCtx).mvarCounter == before.mvarCounter &&
      (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "invalid cache entry triggered fallback or changed caller state"
  let unsupported target := pure (.error
    (Hex.RealFormula.Reify.Error.unsupported target "test unsupported base"))
  let .error (.unsupported subject "test unsupported base") ←
      (AlgebraicRoot.identify q(Real.sqrt (3 + Real.sqrt 2))
        q(3 + Real.sqrt 2) 2 unsupported limit).run |
    throwError "base refusal was not preserved"
  unless subject == q((3 : ℝ) + Real.sqrt 2) do
    throwError "base refusal named the synthetic goal"
  let precise _ := pure (.error
    (Hex.RealFormula.Reify.Error.unsupported q(Real.sin 0) "test offending subterm"))
  let .error (.unsupported subject "test offending subterm") ←
      (AlgebraicRoot.identify q(Real.sqrt (3 + Real.sqrt 2))
        q(3 + Real.sqrt 2) 2 precise limit).run |
    throwError "inner subterm refusal was not preserved"
  unless subject == q(Real.sin 0) do throwError "precise inner subject was replaced"

example : ∀ x : ℝ, x ^ 2 + Real.sqrt (-Real.sqrt 2) ≥ 0 := by
  run_tac do
    let original ← Lean.Elab.Tactic.getGoals
    let before ← getMCtx
    let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let failure ← tryCatchRuntimeEx (do
      Hex.RCF.evalRCFTac (← `(tactic| rcf))
      pure none) fun error => do
        if error.isRuntime || error.isInterrupt then throw error
        pure (some error)
    let some error := failure | throwError "negative-base tactic unexpectedly succeeded"
    unless (← error.toMessageData.toString).startsWith
        "rcf: symbolic or non-rational coefficient" do
      throwError "negative-base final diagnostic changed: {error.toMessageData}"
    unless (← Lean.Elab.Tactic.getGoals) == original &&
        (← getMCtx).mvarCounter == before.mvarCounter &&
        (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "negative-base final decline changed caller state"
  intro x
  positivity

run_elab do
  let before ← getMCtx
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let .error (.budget exhausted) ←
      withOptions (CommonTactic.rcf.algebraic.commonDegree.set · 2) <|
        Coefficients.prepare q(∀ x : ℝ, x ^ 2 + Real.sqrt (Real.sqrt 2) > 0) |
    throwError "nested root did not exhaust its degree admission"
  unless exhausted.dimension == .exponent && exhausted.limit == 2 &&
      exhausted.consumed == 2 && exhausted.requested == 4 do
    throwError "nested root degree admission returned the wrong budget report"
  unless (← getMCtx).mvarCounter == before.mvarCounter &&
      (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "nested root degree exhaustion changed caller state"
  let .ok repeated ← withOptions (CommonTactic.rcf.algebraic.commonDegree.set · 4) <|
      Coefficients.prepare q(∀ x : ℝ,
        x ^ 2 + Real.sqrt (Real.sqrt 2) - (2 : ℝ) ^ (1 / 4 : ℝ) = x ^ 2) |
    throwError "rational and algebraic aliases charged the same selected anchor twice"
  let _ ← repeated.proveReplay
  let .ok guarded ← Coefficients.prepare q(∀ x : ℝ,
      x ^ 2 + Real.sqrt (1 / (4 + Real.sqrt 2)) > 0) |
    throwError "guarded root source failed preparation"
  let mut found := false
  for i in [:guarded.source.divisors.size] do
    if ← isDefEq guarded.source.divisors[i]! q((4 : ℝ) + Real.sqrt 2) then
      found := true
      let _ ← Hex.RCF.checkProof `Hex.RCF.AlgebraicRoots.originalGuard
        q((4 : ℝ) + Real.sqrt 2 ≠ 0) guarded.divisorProofs[i]!
  unless found do throwError "guarded root omitted the exact original divisor"

run_elab do
  let zeroTargets := #[
    q(∀ x : ℝ, x ^ 2 + Real.sqrt (0 / (Real.sqrt 2 - Real.sqrt 2)) ≥ 0),
    q(∀ x : ℝ, x ^ 2 + 0 * Real.sqrt (1 / (Real.sqrt 2 - Real.sqrt 2)) ≥ 0),
    q(∀ x : ℝ, x / Real.sqrt (Real.sqrt 2 - Real.sqrt 2) = 0),
    q(∀ x : ℝ, x ^ 2 + Real.sqrt (Real.sqrt 2 + 1 / (2 - 2)) ≥ 0)]
  let unsupportedTargets := #[
    q(∀ x : ℝ, x ^ 2 + (Real.sqrt 2) ^ (1 / (2 - 2) : ℝ) ≥ 0),
    q(∀ x : ℝ, x ^ 2 + Real.sqrt (Real.sin 0 + Real.sqrt 2) ≥ 0),
    q(∀ x : ℝ, x ^ 2 + Real.sqrt (x + Real.sqrt 2) ≥ 0)]
  let negativeTargets := #[
    q(∀ x : ℝ, x ^ 2 + Real.sqrt (-Real.sqrt 2) ≥ 0),
    q(∀ x : ℝ, x ^ 2 + (-(3 + Real.sqrt 2)) ^ (1 / 3 : ℝ) ≥ 0)]
  for target in zeroTargets ++ unsupportedTargets ++ negativeTargets do
    let before ← getMCtx
    let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let outcome ← tryCatchRuntimeEx
      (Except.ok <$> Coefficients.prepare target) fun error => do
        if error.isRuntime || error.isInterrupt then throw error
        pure (.error (← error.toMessageData.toString))
    if zeroTargets.contains target then
      match outcome with
      | .error "rcf: original closed divisor is zero" => pure ()
      | .ok (.error (.unsupported _ "division by zero is unsupported")) => pure ()
      | _ => throwError "zero-divisor source did not fail with its guard diagnostic: {target}\n{match outcome with
          | .error message => m!"{message}"
          | .ok (.error error) => error.toMessageData
          | .ok (.ok _) => m!"accepted"}"
    else if negativeTargets.contains target then
      match outcome with
      | .ok (.error (.unsupported _ "negative algebraic root base")) => pure ()
      | _ => throwError "negative base lost its structured reason"
    else
      match outcome with
      | .ok (.error (.unsupported _ _)) => pure ()
      | _ => throwError "unsupported source did not return a structured decline: {target}"
    unless (← getMCtx).mvarCounter == before.mvarCounter do
      throwError "failed preparation changed caller metavariables"
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "failed preparation retained auxiliary declarations"
  for target in negativeTargets do
    let saved ← saveState
    let (outcome, _) ← tryFinally' (CommonTactic.handle target) (fun _ => saved.restore)
    match outcome with
    | .declined => pure ()
    | _ => throwError "unsupported algebraic base stopped later handlers"

run_elab do
  let (_, _, value) ← FieldRuntime.coefficient q((2 : ℝ) ^ (1 / 4 : ℝ))
  let p := value.toAlgebraic.p
  let s := value.toAlgebraic.rep.1.square
  if hw : atomWitness p s then
    if hp : (mahlerPrec p : Int) ≤ s.prec then
      let v := PolyQuot.ofSquare p s (DensePoly.ofList [0, 1]) hw hp
      let base := v ^ 2
      let some table := FieldBuild.buildTable p s hw hp [v, base, -v] |
        throwError "selected-root sign fixture failed production"
      unless CommonPresentation.checkRoot table base 2 2 &&
          CommonPresentation.checkRoot table v base 2 do
        throwError "correct nested root coordinates were refused"
      if CommonPresentation.checkRoot table (-v) base 2 then
        throwError "negative conjugate passed nonnegative branch selection"
      if CommonPresentation.checkRoot table v 2 2 then
        throwError "wrong base identity was accepted"
      if CommonPresentation.checkRoot table v 1 0 then
        throwError "zero root degree was accepted"
      if CommonPresentation.checkRoot {table with entries := []} v base 2 then
        throwError "missing recorded root sign was accepted"
    else throwError "selected-root fixture has insufficient precision"
  else throwError "selected-root fixture has no checked witness"

run_elab do
  let .ok selected ← (AlgebraicRoot.identify q(Real.sqrt (3 + Real.sqrt 2))
      q(3 + Real.sqrt 2) 2 Coefficients.prepare
      (CommonTactic.rcf.algebraic.commonDegree.get (← getOptions))).run |
    throwError "correct root source failed authentication"
  let .ok conjugate ← (AlgebraicRoot.identify q(Real.sqrt (3 - Real.sqrt 2))
      q(3 - Real.sqrt 2) 2 Coefficients.prepare
      (CommonTactic.rcf.algebraic.commonDegree.get (← getOptions))).run |
    throwError "positive conjugate fixture failed authentication"
  let p := selected.value.toAlgebraic.p
  let s := selected.value.toAlgebraic.rep.1.square
  let wrong := conjugate.value.toAlgebraic.rep.1.square
  unless conjugate.value.toAlgebraic.p == p do
    throwError "wrong-conjugate fixture did not share the defining polynomial"
  if hw : atomWitness p s then
    if hp : (mahlerPrec p : Int) ≤ s.prec then
      let v := PolyQuot.ofSquare p s (DensePoly.ofList [0, 1]) hw hp
      let some table := FieldBuild.buildTable p s hw hp
          [CommonPresentation.discSlack s v, CommonPresentation.discSlack wrong v] |
        throwError "wrong-conjugate fixture failed sign production"
      unless CommonPresentation.checkEntry hw hp table (ZPoly.toRatPoly p) s v do
        throwError "correct selected embedding was refused"
      if CommonPresentation.checkEntry hw hp table (ZPoly.toRatPoly p) wrong v then
        throwError "different positive conjugate of the same polynomial was accepted"
    else throwError "wrong-conjugate fixture has insufficient precision"
  else throwError "wrong-conjugate fixture has no checked witness"

run_elab do
  let target := q(∀ x : ℝ, x ^ 2 + Real.sqrt (Real.sqrt 2) < 0)
  let prepared ← match ← Coefficients.prepare target with
    | .ok prepared => pure prepared
    | .error error => throwError "false fixture failed preparation: {error.toMessageData}"
  letI : ZPoly.CheckedIrreducible prepared.polynomial := prepared.checked
  if real : prepared.square.meetsRealAxis = true then do
    let input : Replay.Input prepared.polynomial prepared.square prepared.witness
        prepared.precision Unit prepared.arity :=
      ⟨prepared.values, prepared.formula, prepared.quantifier, prepared.divisors, ()⟩
    let options ← getOptions
    let depth := FieldLiteral.rcf.algebraic.directDepth.get options
    let certificate ← match Replay.build input real depth
        (FieldLiteral.rcf.algebraic.maxDoublings.get options)
        (FieldLiteral.rcf.algebraic.monicCore.get options) with
      | .ok result => pure result
      | .error error => throwError "false fixture failed native production: {repr error}"
    unless Replay.check input certificate == .ok false do
      throwError "false fixture did not have an accepted false certificate"
  else throwError "false fixture has no real embedding"
  let outcome ← tryCatchRuntimeEx (Except.ok <$> CommonTactic.handle target) fun error => do
    if error.isRuntime || error.isInterrupt then throw error
    pure (.error (← error.toMessageData.toString))
  match outcome with
  | .error "rcf: the universal sentence is false on the prepared cells" => pure ()
  | .ok (.failed message) =>
      unless (← message.toString).contains "false" do
        throwError "accepted false certificate failed for another reason"
  | _ => throwError "accepted false certificate lost its terminal false diagnostic"

end Hex.RCF.AlgebraicRoots
