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

/- The public quotation entrypoint checks the supplied acceptance equation
and transports it to the canonical checker. This reuses checked fixture/codec
laws, rather than fresh literal reduction or automatic record discovery. -/
private meta def rejected (expected : String) (action : MetaM Expr) : MetaM Bool :=
  fun metaContext metaState coreContext coreState => do
    try
      let _ ← action metaContext metaState coreContext coreState
      return false
    catch error =>
      if error.isInterrupt || error.isMaxHeartbeat || error.isMaxRecDepth then throw error
      unless (← error.toMessageData.toString).startsWith expected do throw error
      return true
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
  let program ← elabTerm (← `(CellOperations.accept? Operations.operations parent.codec values formula [] cert
    .existsReal CompleteQuote.rootGraph CompleteQuote.cells)) none
  synthesizeSyntheticMVarsNoPostponing
  let program ← instantiateMVars program
  let proof ← CellQuote.finishOperations target program (Lean.mkConst ``Operations.accepted)
    (Lean.mkConst ``original) identity
  let name := `Hex.RCF.RealCoefficients.CellReplayTests.OperationsKernel.source
  let proof ← Hex.RCF.checkProof name target proof
  addDecl (.thmDecl {name, levelParams := [], type := target, value := proof})
  let falseProgram ← elabTerm (← `(CellOperations.accept? Operations.operations parent.codec values formula [] cert
    .forallReal CompleteQuote.rootGraph CompleteQuote.cells)) none
  let wrongGoal ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 3 ≥ 0 ∧ x ^ 2 - Real.sqrt 3 ≤ 0 ∧ (0 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let falseProgram ← instantiateMVars falseProgram
  let wrongGoal ← instantiateMVars wrongGoal
  let trivial ← mkAppM ``Option.some #[Lean.mkConst ``Unit.unit]
  for (goal,program,candidate,expected) in [
      (target,falseProgram,Lean.mkConst ``Operations.false_refused,"(kernel) application type mismatch"),
      (target,trivial,← mkEqRefl trivial,"rcf: expected the supplied-operation complete checker"),
      (target,program,Lean.mkConst ``True.intro,"(kernel) application type mismatch"),
      (wrongGoal,program,Lean.mkConst ``Operations.accepted,
        "rcf: handler CellQuote.valuationIdentity proposed a proof of a different goal")] do
    let before := (← getMCtx).decls.toList.length
    let declarations := (← getEnv).checked.get.constants.map₂.toList.length
    unless ← rejected expected
        (CellQuote.finishOperations goal program candidate (Lean.mkConst ``original) identity) do
      throwError "supplied quotation accepted a false/malformed predicate, wrong proof or changed source"
    unless (← getMCtx).decls.toList.length == before &&
        (← getEnv).checked.get.constants.map₂.toList.length == declarations do
      throwError "failed supplied quotation leaked metavariables or proof declarations"
#operation_source_quote

run_meta do
  let .thmInfo declaration ← getConstInfo ``source | throwError "expected actual original-goal proof"
  let _ ← Hex.RCF.checkProof ``source declaration.type declaration.value
  let axioms ← collectAxioms ``source
  unless axioms.size == 3 && axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "unexpected original-goal quotation axioms"
  let seen ← Hex.RCF.ProofEvidence.projectDependencies #[``source]
  for required in #[``CellOperations.check_eq, ``Operations.accepted, ``Operations.checked, ``CompleteReplay.check_sound,
      ``RowOperations.retarget_read, ``CompleteReplay.check_covered] do
    unless seen.contains required do throwError "original-goal proof omitted actual supplied-operation law: {required}"
  for forbidden in #[``CompleteQuote.source, ``Check.source, ``Operations.source,
      ``CellBuild.build, ``ScalarPacket.build, ``ScalarPacket.buildLiteral] do
    if seen.contains forbidden then throwError "original-goal proof reused a source witness or producer: {forbidden}"
  logInfo "fresh original-goal quotation checked; supplied-operation equality, rollback/refusals and standard three axioms retained"
end Hex.RCF.RealCoefficients.CellReplayTests.OperationsKernel
