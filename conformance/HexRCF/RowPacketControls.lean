/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellQuoteStages
open Lean Meta Qq Hex Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RowPacketControls
open Hex.RCF.CellQuoteStages
open Hex.RCF.RealCoefficients.CellReplayTests

/-- The original zero row's graph is retained, but its ordered query is 1. -/
def wrongRow : Codec.Json := .arr #[.number 1, ZeroLiterals.j7,
  .arr #[ZeroLiterals.j12], ZeroLiterals.j5, ZeroLiterals.j56]
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta do
  withoutExporting do
    let rowStarted ← IO.mkRef false
    let validatedAfterQuery ← IO.mkRef false
    let decode : RootQuote.DecoderM := fun expression => do
      if expression.getAppFn.isConstOf ``Dag.validate? && (← rowStarted.get) then
        validatedAfterQuery.set true
      if let some proof ← RowQuote.decoder expression then return some proof
      if let some proof ← SignatureQuote.decoder q(base.signature)
          (mkConst ``signatureData) (mkConst ``signature_literal) expression then
        return some proof
      liftM (RationalQuote.decoder (mkConst ``registry) expression)
    let descriptor := q(CellOperations.selected operations base.codec ZeroLiterals.j7 ZeroLiterals.j30)
    let queries : Q(List base.Poly) := q([0])
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let before ← getMCtx
    let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let basic : Hex.RealFormula.Reify.Config := {}
    let config := {basic with ring := {basic.ring with budget :=
      {basic.ring.budget with proofNodes := 2000000}}}
    let .error (.providerFailure (.invalidProviderEvidence ⟨key,version⟩ reason) _) ←
        RootQuote.runWith (do
          sentinel.mvarId!.assign (mkNatLit 95)
          let root ← RootQuote.quoteWith descriptor decode
          let reader ← mkAppM ``RowOperations.read #[q(base.codec),
            q(Hex.RealClosure.Tower.Signature.codec), q(base.sign), q(base.signature),
            root.value, queries, mkConst ``wrongRow]
          rowStarted.set true
          RowQuote.withDecoder decode fun decoder => do
            let _ ← decoder reader
            throwError "changed row queries returned a proposal") config
      | throwError "changed row queries did not retain their structured rejection"
    unless key == `Hex.RCF.RealCoefficients.RowQuote && version == 0 do
      throwError "changed row query rejection came from {key}/{version}: {reason}"
    if ← validatedAfterQuery.get then
      throwError "changed row queries reached graph validation after rejection"
    let after ← getMCtx
    unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
        before.lmvarCounter == after.lmvarCounter && before.eAssignment.toList == after.eAssignment.toList &&
        before.lAssignment.toList == after.lAssignment.toList &&
        before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst &&
        (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "rejected row queries retained caller state or declarations"
    logInfo "changed ordered row queries rejected before graph validation; structured failure and full rollback checked"
end Hex.RCF.RowPacketControls
