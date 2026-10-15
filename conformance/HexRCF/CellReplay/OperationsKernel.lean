/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients
import HexRCF.CellReplay.Operations
namespace Hex.RCF.RealCoefficients.CellReplayTests.OperationsKernel
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Schema
open Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Canonical
open Hex.RCF.RealCoefficients.CellReplayTests.Algebraic
open Lean Meta Elab Command Term
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/- Quotation transports the actual supplied-operation acceptance equation to
its canonical checker. It reuses checked fixture/codec laws and does not claim
fresh literal-reader reduction or automatic record discovery. -/
elab "#operation_source_quote" : command => liftTermElabM do
  let target ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 2 ≥ 0 ∧ x ^ 2 - Real.sqrt 2 ≤ 0 ∧ (0 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let .ok source ← Reify.prepare target | throwError "original source was not recognized"
  let valuation ← elabTerm (← `(fun i : Fin 1 => original.value (values i))) none
  synthesizeSyntheticMVarsNoPostponing
  let valuation ← instantiateMVars valuation
  let identity ← elabTermEnsuringType (← `(by funext i; fin_cases i; exact coefficient))
    (← mkEq valuation source.valuation)
  synthesizeSyntheticMVarsNoPostponing
  let identity ← instantiateMVars identity
  let checker ← elabTerm (← `(CompleteReplay.check parent.codec values formula [] cert .existsReal
    CompleteQuote.rootGraph CompleteQuote.cells)) none
  let equality ← elabTerm (← `(CellOperations.check_eq Operations.operations parent.codec values formula [] cert
    .existsReal CompleteQuote.rootGraph CompleteQuote.cells)) none
  synthesizeSyntheticMVarsNoPostponing
  let checker ← instantiateMVars checker
  let equality ← instantiateMVars equality
  let accepted ← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[equality], mkConst ``Operations.checked]
  let proof ← CellQuote.finishPacket target checker accepted (mkConst ``original) identity
  let name := `Hex.RCF.RealCoefficients.CellReplayTests.OperationsKernel.source
  let proof ← Hex.RCF.checkProof name target proof
  addDecl (.thmDecl {name, levelParams := [], type := target, value := proof})
#operation_source_quote

run_meta do
  let .thmInfo declaration ← getConstInfo ``source | throwError "expected actual original-goal proof"
  let _ ← Hex.RCF.checkProof ``source declaration.type declaration.value
  let axioms ← collectAxioms ``source
  unless axioms.size == 3 && axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "unexpected original-goal quotation axioms"
  let seen ← Hex.RCF.ProofEvidence.projectDependencies #[``source]
  for required in #[``CellOperations.check_eq, ``Operations.checked, ``CompleteReplay.check_sound,
      ``RowOperations.retarget_read, ``CompleteReplay.check_covered] do
    unless seen.contains required do throwError "original-goal proof omitted actual supplied-operation law: {required}"
  for forbidden in #[``CompleteQuote.source, ``Check.source, ``Operations.source,
      ``CellBuild.build, ``ScalarPacket.build, ``ScalarPacket.buildLiteral] do
    if seen.contains forbidden then throwError "original-goal proof reused a source witness or producer: {forbidden}"
  logInfo "fresh original-goal quotation checked; supplied-operation equality and standard three axioms retained"
end Hex.RCF.RealCoefficients.CellReplayTests.OperationsKernel
