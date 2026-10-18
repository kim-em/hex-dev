/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.TreeQuoteData
public meta import HexRCF.RealCoefficients.RootQuote
public section
namespace Hex.RCF.ReplayHelperTests
open Lean Meta Qq Hex Hex.SignDet Hex.RCF.RealCoefficients
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
@[expose] def diagnose (decision : Bool) (value : Nat) : Except String Nat :=
  if decision = true then .ok value else .ok 23
private meta def restored (before : MetavarContext) (sentinel : Expr)
    (names : Option (Array Name) := none) : MetaM Unit := do
  let after ← getMCtx
  unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.eAssignment.toList == after.eAssignment.toList &&
      before.lAssignment.toList == after.lAssignment.toList &&
      before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst do
    throwError "boundary quotation retained caller metavariables"
  if let some names := names then
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "failed boundary quotation retained declarations"
run_meta do
  let condition : Q(Bool) := q((Replay.leaf Conformance.literalNode).check
    Sturm.orderSign 7 Sturm.Fixtures.p (.finite (-2)) (.finite 2) [])
  let tree : Q(Replay Rat Nat) := q(Replay.leaf Conformance.literalNode)
  -- The element type itself contains a table whose proof depends on replay.
  let hypothesis ← mkEq condition (mkConst ``Bool.true)
  let (element,law) ← withLocalDeclD `accepted hypothesis fun accepted => do
    let law ← mkAppM ``Replay.table_rows #[tree,accepted]
    return (← mkForallFVars #[accepted] (← inferType law),← mkLambdaFVars #[accepted] law)
  let predicate ← withLocalDeclD `unit (mkConst ``Unit) fun unit => mkLambdaFVars #[unit] element
  let kind ← mkAppM ``Subtype #[predicate]
  let entry ← mkAppOptM ``Subtype.mk #[some (mkConst ``Unit),some predicate,
    some (mkConst ``Unit.unit),some law]
  let inline ← mkArrayLit kind [entry]
  let stored ← mkAuxDefinition (← mkFreshUserName `tableEntries) (← inferType inline)
    inline (compile := false)
  -- The helper's fixed type mentions Replay.table, which is absent from its body.
  let checkLaw : Expr := q(RawDescriptor.check_iff (sign := Sturm.orderSign) (context := 7)
    (raw := Conformance.singletonRaw) (evidence := Replay.leaf Conformance.literalNode))
  let wrapper ← withLocalDeclD `proof (← inferType checkLaw) fun proof => do
    withLocalDeclD `decision (mkConst ``Bool) fun decision =>
      mkLambdaFVars #[proof,decision] decision
  let helper ← mkAuxDefinition (← mkFreshUserName `fixedHelper) (← inferType wrapper)
    wrapper (compile := false)
  let info ← getFunInfoNArgs condition.getAppFn condition.getAppNumArgs
  let positions := condition.getAppArgs.zipIdx |>.filterMap fun (_,i) =>
    if info.paramInfo[i]!.binderInfo.isExplicit then some i else none
  unless positions.size == 7 do throwError "replay check changed its explicit signature"
  for mode in [`array,`helper] do
    for (context,result) in [(7,1),(8,23)] do
      let first := mkAppN condition.getAppFn
        (condition.getAppArgs.set! positions[1]! (mkNatLit context))
      let decision ← if mode == `array then do
          let size ← mkAppM ``Array.size #[stored]
          mkAppM ``Bool.and #[first,← mkDecide (← mkEq size (mkNatLit 1))]
        else pure (mkApp2 helper checkLaw first)
      let reader ← mkAppM ``diagnose #[decision,mkNatLit 1]
      let .ok quoted ← RootQuote.quote reader
        | throwError "typed replay helper quotation declined {mode}/{context}"
      let target ← mkEq (← mkAppM ``Except.toOption #[reader])
        (← mkAppM ``Option.some #[mkNatLit result])
      let proof ← Hex.RCF.checkProof `typedHelper target (mkExpectedPropHint quoted.proof target)
      let suffix := if mode == `array then
          (if context == 7 then `arrayTrue else `arrayFalse)
        else (if context == 7 then `helperTrue else `helperFalse)
      addDecl (.thmDecl {
        name := Name.append `Hex.RCF.ReplayHelperTests suffix
        levelParams := []
        type := target
        value := proof})
      let expected := if mode == `array then (if context == 7 then 121420 else 10301)
        else (if context == 7 then 103986 else 9136)
      unless quoted.usage.proofNodes == expected do
        throwError "typed replay helper accounting changed: {mode}/{context}/{quoted.usage.proofNodes}"
      logInfo m!"typed replay helper {mode}/{context}: proofNodes={quoted.usage.proofNodes}"
      if context == 7 then
        let sentinel ← mkFreshExprMVar (mkConst ``Nat)
        let before ← getMCtx
        let action : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
          sentinel.mvarId!.assign (mkNatLit 41)
          RootQuote.quoteWith reader
        let .ok baseline ← RootQuote.runWith action
          | throwError "typed replay helper baseline declined"
        restored before sentinel
        unless baseline.usage == quoted.usage do throwError "typed helper accounting changed"
        let basic : Hex.RealFormula.Reify.Config := {}
        let exactConfig := {basic with ring := {basic.ring with budget :=
          {basic.ring.budget with proofNodes := baseline.usage.proofNodes}}}
        let .ok exactResult ← RootQuote.runWith action exactConfig
          | throwError "typed replay helper exact budget declined"
        unless exactResult.usage == baseline.usage do throwError "typed helper exact usage changed"
        restored before sentinel
        let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
        let small := {exactConfig with ring := {exactConfig.ring with budget :=
          {exactConfig.ring.budget with proofNodes := baseline.usage.proofNodes-1}}}
        let .error (.budget exhausted) ← RootQuote.runWith action small
          | throwError "typed replay helper below-budget input accepted"
        unless exhausted.dimension == .proofNodes do throwError "wrong helper resource exhausted"
        restored before sentinel (some names)
        let touched ← IO.mkRef false
        let rejected ← try
            let _ ← RootQuote.run reader (fun expression => do
              touched.set true
              sentinel.mvarId!.assign (mkNatLit 43)
              if (← inferType expression).isConstOf ``Bool then
                return some (← mkEqRefl (mkConst ``Bool.false))
              return none)
            pure false
          catch _ => pure true
        unless rejected && (← touched.get) do
          throwError "typed replay helper did not reject a wrong-goal proposal"
        restored before sentinel (some names)
        logInfo m!"typed helper exact/below/wrong-goal and caller rollback: {mode}; exact={baseline.usage.proofNodes}"
end Hex.RCF.ReplayHelperTests
