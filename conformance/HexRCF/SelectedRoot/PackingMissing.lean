/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SelectedRoot.PackingReplay

public section

open Hex Hex.RealClosure Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.SelectedRootTests.Data

namespace Hex.RCF.SelectedRootTests.PackingMissing
meta section
open Lean Meta Elab Command Hex.RealClosure.Algebraic

private def checkMissing (index : Nat) : TermElabM Unit := do
  if index == 13 then
    let condition ← Term.withoutErrToSorry (Term.elabTerm (← `(show
        Hex.RCF.SelectedRootTests.PackingReplay.record13.original ≠
          Hex.RCF.SelectedRootTests.PackingReplay.record13.representative ∧
        Hex.RCF.SelectedRootTests.PackingReplay.record6.original =
          Hex.RCF.SelectedRootTests.PackingReplay.record13.representative from by decide +kernel)) none)
    Term.synthesizeSyntheticMVarsNoPostponing
    let condition ← instantiateMVars condition
    let _ ← KernelReplay.auditProof condition (← inferType condition)
    KernelReplay.kernelCheck (← mkFreshUserName `__distinctOriginalWithRetainedKey)
      (← inferType condition) condition
  else if index == 4 then
    let condition ← Term.withoutErrToSorry (Term.elabTerm (← `(show
        Hex.RCF.SelectedRootTests.PackingReplay.record4.original = 0 ∧
        Hex.RCF.SelectedRootTests.PackingReplay.record4.representative = 0 ∧
        Hex.RCF.SelectedRootTests.PackingReplay.record4.sign = 0 from by decide +kernel)) none)
    Term.synthesizeSyntheticMVarsNoPostponing
    let condition ← instantiateMVars condition
    let _ ← KernelReplay.auditProof condition (← inferType condition)
    KernelReplay.kernelCheck (← mkFreshUserName `__originalZeroClaim)
      (← inferType condition) condition
  else if index == 0 then
    let condition ← Term.withoutErrToSorry (Term.elabTerm (← `(show
        Hex.RCF.SelectedRootTests.PackingReplay.record0.original ≠ 0 ∧
        Hex.RCF.SelectedRootTests.PackingReplay.record0.original.natDegree = 0 from by decide +kernel)) none)
    Term.synthesizeSyntheticMVarsNoPostponing
    let condition ← instantiateMVars condition
    let _ ← KernelReplay.auditProof condition (← inferType condition)
    KernelReplay.kernelCheck (← mkFreshUserName `__nonzeroConstantOriginal)
      (← inferType condition) condition
  let retained ← mkAppM ``List.eraseIdx #[mkConst ``Hex.RCF.SelectedRootTests.PackingReplay.facts, toExpr (PackingData.count-(index+1))]
  let context ← Simp.mkContext (simpTheorems := #[← PackingReplay.rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let expression := mkApp (mkConst ``Hex.RCF.SelectedRootTests.Packing.program) retained
  let (simplified, _) ← Meta.simp expression context
  let equation ← simplified.getProof' expression
  let equationType ← mkEq expression simplified.expr
  let _ ← KernelReplay.auditProof equation equationType
  KernelCheck.addChecked (← mkFreshUserName `__missingOriginalReplay) equationType equation
  let collected ← KernelReplay.collectMany 0 (mkConst ``Hex.RCF.SelectedRootTests.Packing.program)
    #[⟨retained⟩] context (fun _ _ => throwError "missing-record control called producer")
  let .missing _ := collected.outcome | throwError "missing original record reached a Boolean verdict"
  let some needed := collected.requests[0]? | throwError "missing request array entry"
  let packet := mkConst (Name.str `Hex.RCF.SelectedRootTests.PackingData s!"packet{index}")
  let key ← mkAppM ``Prod.fst #[packet]
  let valueCodec ← Term.withoutErrToSorry (Term.elabTerm (← `(Data.base.codec)) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let valueCodec ← instantiateMVars valueCodec
  let decoded ← mkAppM ``Codec.readPoly #[valueCodec, key]
  let decoded ← withTransparency .all (whnf decoded)
  unless decoded.getAppFn.isConstOf ``Except.ok do throwError "expected literal original key"
  let expected := decoded.getAppArgs.back!
  KernelReplay.kernelCheck (← mkFreshUserName `__exactMissingOriginal)
    (← mkEq needed.polynomial expected) (← mkEqRefl expected)
  KernelReplay.kernelCheck (← mkFreshUserName `__exactMissingContext)
    (← mkEq needed.context (mkConst ``Data.native)) (← mkEqRefl (mkConst ``Data.native))
  logInfo m!"missing original packet {index} refused before verdict; exact request checked; fuel=0"

elab "#missing_original_reduction" : command => liftTermElabM (checkMissing 13)
elab "#missing_original_zero" : command => liftTermElabM (checkMissing 4)
elab "#missing_original_constant" : command => liftTermElabM (checkMissing 0)
end
/-- info: missing original packet 13 refused before verdict; exact request checked; fuel=0 -/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
#missing_original_reduction
/-- info: missing original packet 4 refused before verdict; exact request checked; fuel=0 -/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
#missing_original_zero
/-- info: missing original packet 0 refused before verdict; exact request checked; fuel=0 -/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
#missing_original_constant

set_option maxRecDepth 32768 in
/-- The swapped packets share all scalar fields and have different originals. -/
theorem jointKeys :
    PackingData.packet13.2.1 = PackingData.packet6.2.1 ∧
    PackingData.packet13.2.2.1 = PackingData.packet6.2.2.1 ∧
    PackingData.packet13.2.2.2.1 = PackingData.packet6.2.2.2.1 ∧
    PackingData.packet13.1 ≠ PackingData.packet6.1 := by
  exact ⟨rfl, rfl, rfl, by decide +kernel⟩

/-- The equal retained key cannot authenticate another original's joint query. -/
def jointSwapped : Bool :=
  let (original, kept, sign, scalar, _) := PackingData.packet13
  let (_, _, _, _, joint) := PackingData.packet6
  (Packing.readRecord original kept sign scalar joint).isNone

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
#selected_parse Hex.RCF.SelectedRootTests.PackingMissing.jointSwappedRejected := jointSwapped

end Hex.RCF.SelectedRootTests.PackingMissing
