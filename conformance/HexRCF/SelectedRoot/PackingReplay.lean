/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.Packing
import HexRCF.SelectedRoot.PackingData
import HexRCF.SelectedRoot.RowTools
import HexRealClosureMathlib.KernelReplay

open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests Hex.RCF.SelectedRootTests.Data Hex.RCF.SelectedRootTests.Upper

/-! Reduced record definitions and the inventory are kernel checked as data.
The named `read` laws retain their provenance from the supplied packets and
recheck those conversions under the native-producer diagnostic guard. -/
namespace Hex.RCF.SelectedRootTests.PackingReplay
meta section
open Lean Meta Elab Command Hex.RealClosure.Algebraic

def rules : MetaM SimpTheorems := do
  let mut rules ← RowTools.rules
  rules ← rules.addDeclToUnfold ``Hex.RCF.SelectedRootTests.Packing.program
  rules ← rules.addDeclToUnfold ``Hex.RCF.SelectedRootTests.Packing.evaluate
  return rules

private def readExpression (index : Nat) (expression : Expr) : MetaM Expr := do
  let result ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (whnf expression)
  let simpContext ← Simp.mkContext (simpTheorems := #[← ReplayTools.rules])
    (config := { decide := false }) (congrTheorems := ← getSimpCongrTheorems)
  let (simplified, _) ← Meta.simp result simpContext
  let equation ← simplified.getProof' result
  let reduced ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (reduce simplified.expr)
  unless reduced.getAppFn.isConstOf ``Option.some do
    throwError "supplied original packing rejected or stuck at {reduced.getAppFn}"
  let record := reduced.getAppArgs.back!
  let type ← inferType record
  let name := Name.str `Hex.RCF.SelectedRootTests.PackingReplay s!"record{index}"
  let declaration := Declaration.defnDecl {
    name, levelParams := [], type, value := record, hints := .regular 0, safety := .safe }
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let _ ← KernelReplay.auditProof record type
  let env ← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true)
  setEnv env
  compileDecl declaration (logErrors := true)
  let checkedResult ← mkAppM ``Option.some #[mkConst name]
  let conversionType ← mkEq expression checkedResult
  let _ ← KernelReplay.auditProof equation conversionType
  KernelCheck.addChecked (Name.str `Hex.RCF.SelectedRootTests.PackingReplay s!"read{index}")
    conversionType equation
  return mkConst name

private def run : TermElabM Unit := do
  let mut facts ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (Algebraic.Packing Data.native)))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  facts ← instantiateMVars facts
  for i in [:PackingData.count] do
    let packet := mkConst (Name.str `Hex.RCF.SelectedRootTests.PackingData s!"packet{i}")
    let p ← mkAppM ``Prod.fst #[packet]
    let rest ← mkAppM ``Prod.snd #[packet]
    let kept ← mkAppM ``Prod.fst #[rest]
    let rest ← mkAppM ``Prod.snd #[rest]
    let claimed ← mkAppM ``Prod.fst #[rest]
    let rest ← mkAppM ``Prod.snd #[rest]
    let scalar ← mkAppM ``Prod.fst #[rest]
    let joint ← mkAppM ``Prod.snd #[rest]
    let record ← readExpression i (mkAppN (mkConst ``Hex.RCF.SelectedRootTests.Packing.readRecord)
      #[p, kept, claimed, scalar, joint])
    facts ← mkAppM ``List.cons #[record, facts]
  let name := `Hex.RCF.SelectedRootTests.PackingReplay.facts
  let type ← inferType facts
  let declaration := Declaration.defnDecl {
    name, levelParams := [], type, value := facts, hints := .regular 0, safety := .safe }
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let _ ← KernelReplay.auditProof facts type
  let env ← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true)
  setEnv env
  compileDecl declaration (logErrors := true)
  let simpContext ← Simp.mkContext (simpTheorems := #[← rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let collected ← KernelReplay.collectMany 0 (mkConst ``Hex.RCF.SelectedRootTests.Packing.program)
    #[⟨mkConst name⟩] simpContext
    (fun _ _ => throwError "frozen original-packing replay called producer")
  unless collected.requests.isEmpty do throwError "frozen original-packing replay has requests"
  match collected.outcome with
  | .checked true proof axioms =>
    KernelCheck.addChecked `Hex.RCF.SelectedRootTests.PackingReplay.accepted
      (← mkEq (mkApp (mkConst ``Hex.RCF.SelectedRootTests.Packing.program) (mkConst name))
        (mkConst ``Bool.true)) proof
    logInfo m!"frozen original-packing row accepted; records={PackingData.count}; fuel=0; requests=0; axioms={axioms}"
  | .checked false .. => throwError "frozen original-packing row rejected"
  | .missing application => throwError "frozen original-packing row incomplete: {application}"

elab "#frozen_original_packings" : command => liftTermElabM run
end
/-- info: frozen original-packing row accepted; records=43; fuel=0; requests=0; axioms=[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
#frozen_original_packings

theorem exists_nested : ∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 :=
  Hex.RCF.SelectedRootTests.Packing.source facts accepted

/-- info: 'Hex.RCF.SelectedRootTests.PackingReplay.exists_nested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_nested
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem vanished : record42.original ≠ 0 ∧ record42.representative = 0 ∧ record42.sign = 0 := by
  decide +kernel

theorem valueZero : record42.value = 0 := by
  rfl

theorem storedZero : record42.value.polynomial = 0 := by
  rw [record42.stored, vanished.2.2]
  rfl
end Hex.RCF.SelectedRootTests.PackingReplay
