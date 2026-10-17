/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.RootQuote
import HexRCF.RealCoefficients.Replay
import HexRCF.CellReplay.Algebraic.Inputs
import HexRCF.CellReplay.Algebraic.Records
import HexRCF.RealCoefficients.RationalQuote
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RootTableQuoteTests
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

def literal : Except Hex.RCF.RealCoefficients.Replay.Error Nat := .ok 7

def badLiteral : Except Hex.RCF.RealCoefficients.Replay.Error Nat := .error .evidence

run_meta do
  withExporting (isExporting := false) do
    let .ok result ← RootQuote.quote (mkConst ``literal)
      | throwError "structured-error success reader failed"
    let statement ← mkEq (← mkAppM ``Except.toOption #[mkConst ``literal])
      (← mkAppM ``Option.some #[mkNatLit 7])
    let proof ← Hex.RCF.checkProof `structuredReader statement result.proof
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.RootTableQuoteTests.literal_read,levelParams := [],
        type := statement,value := proof})
    let .error (.providerFailure (.invalidProviderEvidence ..) _) ←
        RootQuote.quote (mkConst ``badLiteral)
      | throwError "structured-error failure reader was accepted"
    logInfo m!"structured-error reader checked; proofNodes={result.usage.proofNodes}"
end Hex.RCF.RootTableQuoteTests
