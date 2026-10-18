/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.TreeQuoteData
public meta import HexRCF.RealCoefficients.RootQuote
public section
namespace Hex.RCF.ReplayBoundaryTests
open Lean Meta Qq Hex Hex.SignDet Hex.RCF.RealCoefficients
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
@[expose] def guard (decision : Bool) : Except String Unit :=
  if decision = true then .ok () else .error "replay declined"
theorem guard_true (decision : Bool) (value : Unit)
    (accepted : (guard decision).toOption = some value) : decision = true := by
  cases decision <;> simp_all [guard, Except.toOption]
@[expose] def consume (decision : Bool) (value : Nat) : Except String Nat :=
  if decision = true then .ok value else .error "replay declined"
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
  let subject ← mkAppM ``guard #[condition]
  let .ok quoted ← RootQuote.quote subject
    | throwError "dependent-boundary guard quotation declined"
  let accepted ← mkAppM ``guard_true #[condition,quoted.value,quoted.proof]
  let target ← mkEq condition (mkConst ``Bool.true)
  let accepted ← Hex.RCF.checkProof `checkedLeaf target accepted
  let tree : Q(Replay Rat Nat) := q(Replay.leaf Conformance.literalNode)
  let predicate ← withLocalDeclD `tree (← inferType tree) fun node => do
    let fields := condition.getAppArgs
    let check := mkAppN condition.getAppFn (fields.set! (fields.size-1) node)
    mkLambdaFVars #[node] (← mkEq check (mkConst ``Bool.true))
  let subtype ← mkAppM ``Subtype #[predicate]
  let entry ← mkAppOptM ``Subtype.mk #[some (← inferType tree),some predicate,some tree,some accepted]
  let inline ← mkArrayLit subtype [entry]
  let kind ← inferType inline
  let stored ← mkAuxDefinition (← mkFreshUserName `checkedEntries) kind inline (compile := false)
  let info ← getFunInfoNArgs condition.getAppFn condition.getAppNumArgs
  let positions := condition.getAppArgs.zipIdx |>.filterMap fun (_,i) =>
    if info.paramInfo[i]!.binderInfo.isExplicit then some i else none
  unless positions.size == 7 do throwError "replay check changed its explicit signature"
  for (mode,values) in [(`inline,inline),(`stored,stored)] do
    for (context,result) in [(7,1),(8,23)] do
      let first := mkAppN condition.getAppFn
        (condition.getAppArgs.set! positions[1]! (mkNatLit context))
      let size ← mkAppM ``Array.size #[values]
      let second ← mkDecide (← mkEq size (mkNatLit 1))
      let composite ← mkAppM ``Bool.and #[first,second]
      let reader ← mkAppM ``diagnose #[composite,mkNatLit 1]
      let .ok quoted ← RootQuote.quote reader
        | throwError "dependent-boundary quotation declined {mode}/{context}"
      let target ← mkEq (← mkAppM ``Except.toOption #[reader])
        (← mkAppM ``Option.some #[mkNatLit result])
      let proof ← Hex.RCF.checkProof `dependentBoundary target (mkExpectedPropHint quoted.proof target)
      let suffix := if mode == `inline then
          (if context == 7 then `inlineTrue else `inlineFalse)
        else (if context == 7 then `storedTrue else `storedFalse)
      let name := Name.append `Hex.RCF.ReplayBoundaryTests suffix
      addDecl (.thmDecl {name,levelParams := [],type := target,value := proof})
      logInfo m!"dependent replay helper {mode}/{context}: proofNodes={quoted.usage.proofNodes}"
      if mode == `stored && context == 7 then
        let sentinel ← mkFreshExprMVar (mkConst ``Nat)
        let before ← getMCtx
        let action : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
          sentinel.mvarId!.assign (mkNatLit 41)
          RootQuote.quoteWith reader
        let .ok baseline ← RootQuote.runWith action
          | throwError "dependent-boundary baseline declined"
        restored before sentinel
        unless baseline.usage.proofNodes == 86763 do
          throwError "dependent-boundary accounting changed: {baseline.usage.proofNodes}"
        let basic : Hex.RealFormula.Reify.Config := {}
        let exactConfig := {basic with ring := {basic.ring with budget :=
          {basic.ring.budget with proofNodes := baseline.usage.proofNodes}}}
        let .ok exactResult ← RootQuote.runWith action exactConfig
          | throwError "dependent-boundary exact budget declined"
        unless exactResult.usage == baseline.usage do throwError "boundary accounting changed"
        restored before sentinel
        let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
        let small := {exactConfig with ring := {exactConfig.ring with budget :=
          {exactConfig.ring.budget with proofNodes := baseline.usage.proofNodes-1}}}
        let .error (.budget exhausted) ← RootQuote.runWith action small
          | throwError "dependent-boundary below-budget input accepted"
        unless exhausted.dimension == .proofNodes do throwError "wrong boundary resource exhausted"
        restored before sentinel (some names)
        let rejected ← try
            let _ ← RootQuote.run reader (fun expression => do
              sentinel.mvarId!.assign (mkNatLit 43)
              if (← inferType expression).isConstOf ``Bool then
                return some (← mkEqRefl (mkConst ``Bool.false))
              return none)
            pure false
          catch _ => pure true
        unless rejected do throwError "dependent boundary accepted a wrong-goal proof"
        restored before sentinel (some names)
        logInfo m!"boundary exact/below/wrong-goal and caller rollback checked; exact={baseline.usage.proofNodes}"
end Hex.RCF.ReplayBoundaryTests
