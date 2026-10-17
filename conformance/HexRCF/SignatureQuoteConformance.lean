/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RootQuoteData
public meta import HexRCF.RealCoefficients.RootQuote
public section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.SignatureRoundtrip
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

@[expose] def first := RootQuoteTests.base.signature
@[expose] def second := first.extend (.array .nil)
@[expose] def readFirst := Tower.Signature.codec.decode (Tower.Signature.codec.encode first)
@[expose] def readSecond := Tower.Signature.codec.decode (Tower.Signature.codec.encode second)

run_meta do
  for (readerName,valueName) in [( ``readFirst,``first),( ``readSecond,``second)] do
    let visits ← IO.mkRef (0 : Nat)
    let decoder : RootQuote.DecoderM := fun expression => do
      if let .proj ``ValueCodec 1 codec := expression.getAppFn then
        if codec.isConstOf ``Tower.Signature.codec then visits.modify (·+1)
      return none
    let .ok result ← RootQuote.runWith
        (RootQuote.quoteWith (mkConst readerName) decoder)
      | throwError "default signature roundtrip declined"
    unless (← visits.get) == 0 do throwError "canonical roundtrip reached the caller decoder"
    let statement ← mkEq (← mkAppM ``Except.toOption #[mkConst readerName])
      (← mkAppM ``Option.some #[mkConst valueName])
    let proof ← Hex.RCF.checkProof `signatureRoundtrip statement result.proof
    if readerName == ``readSecond then
      let wrong ← mkEq (← mkAppM ``Except.toOption #[mkConst readerName])
        (← mkAppM ``Option.some #[mkConst ``first])
      let refused ← withoutModifyingEnv do
        try
          let _ ← Hex.RCF.checkProof `wrongSignature wrong (mkExpectedPropHint result.proof wrong)
          pure false
        catch error =>
          if error.isInterrupt || error.isMaxHeartbeat || error.isMaxRecDepth then throw error
          pure true
      unless refused do throwError "a different encoded signature proved the original signature"
    let axioms ← collectAxioms proof.getAppFn.constName!
    unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
      throwError "signature roundtrip axioms changed"
    let config : Hex.RealFormula.Reify.Config := {}
    let exactBudget := {config with ring := {config.ring with budget :=
      {config.ring.budget with proofNodes := result.usage.proofNodes}}}
    let .ok repeated ← RootQuote.runWith
        (RootQuote.quoteWith (mkConst readerName)) exactBudget
      | throwError "signature roundtrip failed at exact budget"
    unless repeated.usage == result.usage do throwError "signature accounting changed"
    let lower := {config with ring := {config.ring with budget :=
      {config.ring.budget with proofNodes := result.usage.proofNodes-1}}}
    let .error (.budget exhausted) ← RootQuote.runWith
        (RootQuote.quoteWith (mkConst readerName)) lower
      | throwError "signature roundtrip did not exhaust one below its budget"
    unless exhausted.dimension == .proofNodes do throwError "signature exhausted another dimension"
    logInfo m!"default signature exact subject: {readerName}; nodes={result.usage.proofNodes}; exact/one-below checked"

end Hex.RCF.SignatureRoundtrip
