/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealClosure.TowerContext
public meta import HexRCF.RealCoefficients.SignatureQuote
public section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.FrozenSignature
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

@[expose] def first : Tower.Signature := ⟨⟨[],0⟩,[]⟩
@[expose] def second := first.extend (.array .nil)
abbrev firstData : Codec.Json :=
  .array (.cons (.array .nil) (.cons (.number 0) (.cons (.array .nil) .nil)))
abbrev secondData : Codec.Json :=
  .array (.cons (.array .nil) (.cons (.number 0)
    (.cons (.array (.cons (.array .nil) .nil)) .nil)))
theorem first_literal : firstData = first.literal.toJson := rfl
theorem second_literal : secondData = second.literal.toJson := rfl
@[expose] def readFirst := Tower.Signature.codec.decode firstData
@[expose] def readSecond := Tower.Signature.codec.decode secondData
@[expose] def readProjected := Tower.Signature.codec.decode
  (#[Codec.Json.Value.array (.cons (.array .nil)
    (.cons (.number (Int.ofNat 0)) (.cons (.array .nil) .nil)))])[0]!

run_meta do
  withoutExporting do
    for (reader,subject,data,binding) in
        [( ``readFirst,``first,``firstData,``first_literal),
         ( ``readSecond,``second,``secondData,``second_literal),
         ( ``readProjected,``first,``firstData,``first_literal)] do
      let visits ← IO.mkRef (0 : Nat)
      let decode : RootQuote.DecoderM := fun expression => do
        let result ← SignatureQuote.decoder (mkConst subject) (mkConst data)
          (mkConst binding) expression
        if result.isSome then visits.modify (·+1)
        return result
      let .ok result ← RootQuote.runWith (RootQuote.quoteWith (mkConst reader) decode)
        | throwError "frozen signature quotation declined"
      unless (← visits.get) > 0 do throwError "frozen signature binding was not consumed"
      let target ← mkEq (← mkAppM ``Except.toOption #[mkConst reader])
        (← mkAppM ``Option.some #[mkConst subject])
      let proof ← Hex.RCF.checkProof `frozenSignature target result.proof
      let kind ← inferType proof
      withExporting (isExporting := true) do
        addDecl (.thmDecl {
          name := reader.appendAfter "_checked",levelParams := [],type := kind,value := proof})
      let config : Hex.RealFormula.Reify.Config := {}
      let exactBudget := {config with ring := {config.ring with budget :=
        {config.ring.budget with proofNodes := result.usage.proofNodes}}}
      let .ok repeated ← RootQuote.runWith (RootQuote.quoteWith (mkConst reader) decode) exactBudget
        | throwError "frozen signature failed at its exact budget"
      unless repeated.usage == result.usage do throwError "frozen signature accounting changed"
      let lower := {config with ring := {config.ring with budget :=
        {config.ring.budget with proofNodes := result.usage.proofNodes-1}}}
      let .error (.budget exhausted) ← RootQuote.runWith
          (RootQuote.quoteWith (mkConst reader) decode) lower
        | throwError "frozen signature did not exhaust one below its budget"
      unless exhausted.dimension == .proofNodes do throwError "frozen signature exhausted another dimension"
      logInfo m!"frozen signature exact subject and exact/one-below budgets: {reader}; nodes={result.usage.proofNodes}"

run_meta do
  for (subject,binding) in [( ``first,``second_literal),( ``second,``first_literal)] do
    let caller ← mkFreshExprMVar (mkConst ``Nat)
    let before ← getMCtx
    let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let refused ← try
      let _ ← RootQuote.runWith do
        caller.mvarId!.assign (mkNatLit 9)
        let _ ← mkFreshExprMVar (mkConst ``Nat)
        let statement ← mkEq (mkNatLit 0) (mkNatLit 0)
        addDecl (.thmDecl {
          name := `Hex.RCF.FrozenSignature.failureMarker,levelParams := [],
          type := statement,value := ← mkEqRefl (mkNatLit 0)})
        RootQuote.quoteWith (mkConst ``readFirst)
          (SignatureQuote.decoder (mkConst subject) (mkConst ``firstData) (mkConst binding))
      pure false
    catch error =>
      if error.isInterrupt || error.isMaxHeartbeat || error.isMaxRecDepth then throw error
      pure true
    unless refused do throwError "a wrong signature literal binding was accepted"
    let after ← getMCtx
    unless !(← caller.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
        before.lmvarCounter == after.lmvarCounter &&
        before.eAssignment.toList == after.eAssignment.toList &&
        before.lAssignment.toList == after.lAssignment.toList &&
        before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst &&
        (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "wrong frozen signature retained caller state"
    logInfo m!"wrong frozen signature binding/subject rejected and caller restored: {subject}/{binding}"

run_meta do
  let action : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
      let reader ← unfoldDefinition? (mkConst ``readSecond)
      let some reader := reader | throwError "frozen signature reader is not exposed"
      let .none ← SignatureQuote.decoder (mkConst ``first) (mkConst ``firstData)
          (mkConst ``first_literal) reader
        | throwError "signature decoder accepted a different literal payload"
      RootQuote.quoteWith (mkConst ``readFirst)
        (SignatureQuote.decoder (mkConst ``first) (mkConst ``firstData) (mkConst ``first_literal))
  let .ok _ ← RootQuote.runWith action
    | throwError "frozen signature declined after an ineligible payload"
  logInfo "different frozen signature payload declines; a later exact quotation succeeds"

end Hex.RCF.FrozenSignature
