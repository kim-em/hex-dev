/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Guards
import HexRCF.RealCoefficients.CellQuote
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.CompleteQuote
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients Schema Canonical
open Lean Meta Elab Command Term
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
local instance : Hashable parent.Value := RowEncode.hashable parent.codec
local instance : Hashable Signature := RowEncode.hashable Signature.codec

/- These laws reuse the independently checked frozen fixture and the finite
codec roundtrip. They do not claim a fresh reduction of the serialized reader. -/
def rootGraph := Codec.graph parent.codec Signature.codec (Dag.encode roots.replay)
def cells := CellEncode.packet parent.codec evidence

theorem checked : CompleteReplay.check parent.codec values formula [] Canonical.cert
    .existsReal rootGraph cells = .ok true := by
  unfold rootGraph cells
  exact (CompleteReplay.check_covered parent.codec values formula [] Canonical.cert roots evidence
    .existsReal (by simp) (parent.codec_lawful.covers _)).trans Check.exists_checked

theorem false_checked : CompleteReplay.check parent.codec values formula [] Canonical.cert
    .forallReal rootGraph cells = .ok false := by
  unfold rootGraph cells
  exact (CompleteReplay.check_covered parent.codec values formula [] Canonical.cert roots evidence
    .forallReal (by simp) (parent.codec_lawful.covers _)).trans Check.forall_false

theorem guarded_checked : CompleteReplay.check parent.codec values formula [Guards.negativeOne]
    Canonical.cert .existsReal rootGraph cells = .ok true := by
  unfold rootGraph cells
  exact (CompleteReplay.check_covered parent.codec values formula [Guards.negativeOne]
    Canonical.cert roots evidence .existsReal (by simpa using Guards.nonzero)
    (parent.codec_lawful.covers _)).trans Guards.accepted

theorem domains : ∀ d ∈ [Guards.negativeOne], original.value d ≠ 0 :=
  CompleteReplay.check_domains original parent.codec values formula [Guards.negativeOne]
    Canonical.cert .existsReal rootGraph cells true guarded_checked

elab "#complete_original_quote" : command => liftTermElabM do
  let target ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 2 ≥ 0 ∧ x ^ 2 - Real.sqrt 2 ≤ 0 ∧ (0 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let source ← match ← Reify.prepare target with
    | .error error => throwError "{Hex.RealFormula.Reify.Error.toMessageData error}"
    | .ok source => pure source
  let valuation ← elabTerm (← `(fun i : Fin 1 => original.value (values i))) none
  synthesizeSyntheticMVarsNoPostponing
  let valuation ← instantiateMVars valuation
  let expected ← mkEq valuation source.valuation
  let identity ← elabTermEnsuringType (← `(by funext i; fin_cases i; exact Schema.coefficient)) expected
  let identity ← instantiateMVars identity
  let checker ← elabTerm (← `(CompleteReplay.check parent.codec values formula [] Canonical.cert
    .existsReal rootGraph cells)) none
  synthesizeSyntheticMVarsNoPostponing
  let checker ← instantiateMVars checker
  let proof ← CellQuote.finishPacket target checker (Lean.mkConst ``checked)
    (Lean.mkConst ``original) identity
  let name := `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.CompleteQuote.source
  let proof ← Hex.RCF.checkProof name target proof
  addDecl (.thmDecl {name, levelParams := [], type := target, value := proof})
  let wrongTarget ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 2 > 0 ∧ x ^ 2 - Real.sqrt 2 ≤ 0 ∧ (0 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let wrongTarget ← instantiateMVars wrongTarget
  let refused ← try
    let _ ← CellQuote.finishPacket wrongTarget checker (Lean.mkConst ``checked)
      (Lean.mkConst ``original) identity
    pure false
  catch _ => pure true
  unless refused do throwError "packet quotation accepted a different original formula"
  -- A false verdict and a typed-only checker cannot enter packet quotation.
  for (candidate,accepted) in #[
      (← elabTerm (← `(CompleteReplay.check parent.codec values formula [] Canonical.cert
        .forallReal rootGraph cells)) none, Lean.mkConst ``false_checked),
      (← elabTerm (← `(CellReplay.check values formula [] Canonical.cert roots evidence .existsReal)) none,
        Lean.mkConst ``Check.exists_checked)] do
    let marker ← mkFreshExprMVar (mkConst ``Nat)
    let before := (← getMCtx).decls.toList.length
    let refused ← try
      let _ ← CellQuote.finishPacket target candidate accepted (Lean.mkConst ``original) identity
      pure false
    catch _ => pure true
    unless refused do throwError "packet quotation accepted a false verdict or a non-packet checker"
    unless (← getMCtx).decls.toList.length == before do throwError "failed packet quotation changed metavariable state"
    unless !(← marker.mvarId!.isAssigned) do throwError "failed packet quotation assigned unrelated state"
#complete_original_quote
#print axioms source

elab "#complete_guarded_quote" : command => liftTermElabM do
  let target ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 2 ≥ 0 ∧ x ^ 2 - Real.sqrt 2 ≤ 0 ∧ 0 / (-1 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let source ← match ← Reify.prepare target with
    | .error error => throwError "{Hex.RealFormula.Reify.Error.toMessageData error}"
    | .ok source => pure source
  let valuation ← elabTerm (← `(fun i : Fin 1 => original.value (values i))) none
  synthesizeSyntheticMVarsNoPostponing
  let valuation ← instantiateMVars valuation
  let identity ← elabTermEnsuringType (← `(by funext i; fin_cases i; exact Schema.coefficient))
    (← mkEq valuation source.valuation)
  let checker ← elabTerm (← `(CompleteReplay.check parent.codec values formula [Guards.negativeOne]
    Canonical.cert .existsReal rootGraph cells)) none
  synthesizeSyntheticMVarsNoPostponing
  let checker ← instantiateMVars checker
  let identity ← instantiateMVars identity
  let refused ← try
    let _ ← CellQuote.finishPacket target checker (Lean.mkConst ``guarded_checked)
      (Lean.mkConst ``original) identity
    pure false
  catch _ => pure true
  unless refused do throwError "complete quotation accepted a missing original divisor identity"
  let zeroTarget ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 2 ≥ 0 ∧ x ^ 2 - Real.sqrt 2 ≤ 0 ∧ 0 / (0 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let refused ← try
    let _ ← CellQuote.finishPacket (← instantiateMVars zeroTarget) checker (Lean.mkConst ``guarded_checked)
      (Lean.mkConst ``original) identity #[Lean.mkConst ``Guards.negativeOne_value]
    pure false
  catch _ => pure true
  unless refused do throwError "complete quotation erased a cancelled original zero divisor"
  let proof ← CellQuote.finishPacket target checker (Lean.mkConst ``guarded_checked)
    (Lean.mkConst ``original) identity #[Lean.mkConst ``Guards.negativeOne_value]
  let name := `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.CompleteQuote.guarded_source
  let proof ← Hex.RCF.checkProof name target proof
  addDecl (.thmDecl {name, levelParams := [], type := target, value := proof})
#complete_guarded_quote
#print axioms guarded_source
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.CompleteQuote
