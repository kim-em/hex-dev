/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.QuotientQuoteData
public meta import HexRCF.RealCoefficients.RootQuote
public section
open Lean Meta Hex.RCF.RealCoefficients
namespace Hex.RCF.QuotientQuote
set_option smartUnfolding false
set_option maxRecDepth 32768

private meta def restored (before : MetavarContext) (sentinel : Expr)
    (names : Option (Array Name) := none) : MetaM Unit := do
  let after ← getMCtx
  unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.eAssignment.toList == after.eAssignment.toList &&
      before.lAssignment.toList == after.lAssignment.toList &&
      before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst do
    throwError "quotient quotation retained caller metavariables"
  if let some names := names then
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "failed quotient quotation retained declarations"

run_meta do
  let sentinel ← mkFreshExprMVar (mkConst ``Nat)
  let before ← getMCtx
  let action : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
    sentinel.mvarId!.assign (mkNatLit 37)
    RootQuote.quoteOptionWith (mkConst ``reader)
  let .ok result ← RootQuote.runWith action | throwError "quotient quotation baseline failed"
  unless result.usage.proofNodes == 92 do
    throwError "quotient quotation budget changed: {result.usage.proofNodes}"
  restored before sentinel
  let basic : Hex.RealFormula.Reify.Config := {}
  let exactConfig := {basic with ring := {basic.ring with budget :=
    {basic.ring.budget with proofNodes := result.usage.proofNodes}}}
  let .ok exactResult ← RootQuote.runWith action exactConfig
    | throwError "quotient quotation failed at its exact budget"
  unless exactResult.usage == result.usage do throwError "quotient quotation accounting changed"
  restored before sentinel
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let small := {exactConfig with ring := {exactConfig.ring with budget :=
    {exactConfig.ring.budget with proofNodes := result.usage.proofNodes-1}}}
  let .error (.budget exhausted) ← RootQuote.runWith action small
    | throwError "quotient quotation accepted one node below its budget"
  unless exhausted.dimension == .proofNodes do throwError "quotient quotation exhausted another resource"
  restored before sentinel (some names)
  let .error (.providerFailure (.invalidProviderEvidence _ _) _) ← RootQuote.runWith (do
      sentinel.mvarId!.assign (mkNatLit 41)
      RootQuote.quoteOptionWith (mkConst ``different))
    | throwError "quotient quotation accepted the wrong term count"
  restored before sentinel (some names)
  let target ← mkEq (mkConst ``reader) (← mkAppM ``Option.some #[mkNatLit 7])
  let proof ← Hex.RCF.checkProof `quotientReader target result.proof
  withExporting (isExporting := true) do
    addDecl (.thmDecl {
      name := `Hex.RCF.QuotientQuote.checked,levelParams := [],type := target,value := proof})
  logInfo m!"quotient-backed formula reader: exact/below budget={result.usage.proofNodes}; rejection and caller rollback checked"

end Hex.RCF.QuotientQuote
