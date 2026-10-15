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

/-- Every failing quotation restores the declaration count and leaves an
unrelated metavariable unassigned, including failures in source preflight. -/
private meta def refuse (label : String) (action : MetaM Expr) : MetaM Unit := do
  let marker ← mkFreshExprMVar (mkConst ``Nat)
  let before := (← getMCtx).decls.toList.length
  let refused ← try
    let _ ← action
    pure false
  catch _ => pure true
  unless refused do throwError "packet quotation unexpectedly accepted: {label}"
  unless (← getMCtx).decls.toList.length == before do
    throwError "failed packet quotation changed metavariable state: {label}"
  unless !(← marker.mvarId!.isAssigned) do
    throwError "failed packet quotation assigned unrelated state: {label}"

/- These laws reuse the independently checked frozen fixture and the finite
codec roundtrip. They do not claim a fresh reduction of the serialized reader. -/
def rootGraph := Codec.graph parent.codec Signature.codec (Dag.encode roots.replay)
def cells := CellEncode.packet parent.codec evidence

#eval (show IO Unit from do
  let encoded := Codec.Json.arr #[rootGraph,cells]
  let frozen := Codec.Json.arr #[Literals.roots, .arr #[Literals.sections,Literals.sectors]]
  unless encoded.writeBytes == frozen.writeBytes do
    throw (IO.userError "checked fixture re-encoding changed its frozen bytes")
  IO.println "checked typed fixture re-encoding matches the frozen complete packet bytes")

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
  let .ok _ ← Reify.prepare wrongTarget
    | throwError "different-formula control failed during source preparation"
  refuse "different original formula" (CellQuote.finishPacket wrongTarget checker
    (Lean.mkConst ``checked) (Lean.mkConst ``original) identity)
  -- A false verdict and a typed-only checker cannot enter packet quotation.
  for (candidate,accepted) in #[
      (← elabTerm (← `(CompleteReplay.check parent.codec values formula [] Canonical.cert
        .forallReal rootGraph cells)) none, Lean.mkConst ``false_checked),
      (← elabTerm (← `(CellReplay.check values formula [] Canonical.cert roots evidence .existsReal)) none,
        Lean.mkConst ``Check.exists_checked)] do
    refuse "false verdict or non-packet checker"
      (CellQuote.finishPacket target candidate accepted (Lean.mkConst ``original) identity)
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
  refuse "missing original divisor identity" (CellQuote.finishPacket target checker
    (Lean.mkConst ``guarded_checked) (Lean.mkConst ``original) identity)
  let zeroTarget ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 2 ≥ 0 ∧ x ^ 2 - Real.sqrt 2 ≤ 0 ∧ 0 / (0 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let zeroTarget ← instantiateMVars zeroTarget
  -- Known zero divisors are rejected during source preflight itself.
  let .error _ ← Reify.prepare zeroTarget
    | throwError "source preflight accepted a cancelled zero divisor"
  -- This tests rollback through the already established source-preflight error.
  refuse "zero-divisor source preflight" (CellQuote.finishPacket zeroTarget checker
    (Lean.mkConst ``guarded_checked) (Lean.mkConst ``original) identity
    #[Lean.mkConst ``Guards.negativeOne_value])
  let mismatched ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 2 ≥ 0 ∧ x ^ 2 - Real.sqrt 2 ≤ 0 ∧ 0 / (-2 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let mismatched ← instantiateMVars mismatched
  let .ok different ← Reify.prepare mismatched
    | throwError "nonzero-divisor identity control failed during source preparation"
  unless different.divisors.size == 1 do
    throwError "nonzero-divisor identity control lost its original guard"
  refuse "different original divisor identity" (CellQuote.finishPacket mismatched checker
    (Lean.mkConst ``guarded_checked) (Lean.mkConst ``original) identity
    #[Lean.mkConst ``Guards.negativeOne_value])
  let proof ← CellQuote.finishPacket target checker (Lean.mkConst ``guarded_checked)
    (Lean.mkConst ``original) identity #[Lean.mkConst ``Guards.negativeOne_value]
  let name := `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.CompleteQuote.guarded_source
  let proof ← Hex.RCF.checkProof name target proof
  addDecl (.thmDecl {name, levelParams := [], type := target, value := proof})
#complete_guarded_quote
#print axioms guarded_source
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.CompleteQuote
