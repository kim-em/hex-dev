/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.ReplayTools
import HexRCF.SelectedRoot.Intermediates
import Lean.Elab.Command

meta section
namespace Hex.RCF.SelectedRootTests.Collect
open Hex.RCF.SelectedRootTests
open Lean Meta Elab Command Hex Hex.RealClosure Hex.SignDet
open Hex.RealClosure.Algebraic

private def control : TermElabM Unit := do
  let mut facts ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (SignFact Data.native)))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  facts ← instantiateMVars facts
  for index in [:Packets.packets.length] do
    let some fact ← ReplayTools.readPacket index | throwError "a frozen literal packet rejected"
    facts ← mkAppM ``List.cons #[fact, facts]
  for index in [:2] do
    let packet := mkConst (Name.str `Hex.RCF.SelectedRootTests.Intermediates s!"packet{index}")
    let polynomial ← mkAppM ``Prod.fst #[packet]
    let rest ← mkAppM ``Prod.snd #[packet]
    let claimed ← mkAppM ``Prod.fst #[rest]
    let graph ← mkAppM ``Prod.snd #[rest]
    let expression := mkAppN (mkConst ``Read.fromPacket?) #[polynomial, claimed, graph]
    let some fact ← ReplayTools.readExpression (22+index) expression | throwError "intermediate packet rejected"
    facts ← mkAppM ``List.cons #[fact, facts]
  logInfo m!"checked literal packets: {Packets.packets.length}"
  let simpContext ← Simp.mkContext (simpTheorems := #[← ReplayTools.rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let raw := mkApp (mkConst ``Read.rawProgram) facts
  let (rawOutcome, _) ← KernelReplay.assemble raw simpContext
  match rawOutcome with
  | .checked value _ _ => logInfo m!"literal subject parsing: {value}"
  | .missing _ => throwError "subject parsing unexpectedly required arithmetic"
  let program := mkConst ``Read.rootProgram
  let collected ← KernelReplay.collectMany 0 program #[⟨facts⟩] simpContext (fun _ _ => pure none)
  match collected.outcome with
  | .checked true proof axioms =>
    let some inventory := collected.inventories[0]? | throwError "missing retained inventory"
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let factsName := `Hex.RCF.SelectedRootTests.Collect.facts
    let factType ← inferType inventory.facts
    let declaration := Declaration.defnDecl {
      name := factsName
      levelParams := []
      type := factType
      value := inventory.facts
      hints := .regular 0
      safety := .safe }
    let env ← ofExceptKernelException <| (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    setEnv env
    compileDecl declaration (logErrors := true)
    let acceptedType ← mkEq (mkApp program (mkConst factsName)) (mkConst ``Bool.true)
    let acceptedName := `Hex.RCF.SelectedRootTests.Collect.rootAccepted
    let _ ← KernelReplay.auditProof proof acceptedType
    let env ← ofExceptKernelException <| (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      (.thmDecl { name := acceptedName, levelParams := [], type := acceptedType, value := proof })
      none (doCheck := true)
    setEnv env
    logInfo m!"root reconstructed: checked=true, requests={collected.requests.size}, axioms={axioms}"
  | .checked false .. => throwError "valid upper root data rejected"
  | .missing application => throwError "reached missing arithmetic: {application}"

elab "#selected_collect" : command => liftTermElabM control
end Hex.RCF.SelectedRootTests.Collect
/--
info: checked literal packets: 22
---
info: literal subject parsing: true
---
info: root reconstructed: checked=true, requests=0, axioms=[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
#selected_collect

/-- info: 'Hex.RCF.SelectedRootTests.Collect.rootAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.SelectedRootTests.Collect.rootAccepted
