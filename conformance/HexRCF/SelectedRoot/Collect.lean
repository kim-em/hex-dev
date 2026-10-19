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
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let factsName := `Hex.RCF.SelectedRootTests.Collect.facts
  let factType ← inferType facts
  let declaration := Declaration.defnDecl {
    name := factsName, levelParams := [], type := factType, value := facts,
    hints := .regular 0, safety := .safe }
  let _ ← KernelReplay.auditProof facts factType
  let env ← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true)
  setEnv env
  compileDecl declaration (logErrors := true)
  logInfo "checked literal packets: 22 plus 2 root intermediates; native unfolds=0"

elab "#selected_collect" : command => liftTermElabM control
end Hex.RCF.SelectedRootTests.Collect
/-- info: checked literal packets: 22 plus 2 root intermediates; native unfolds=0 -/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
#selected_collect
