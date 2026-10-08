/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SelectedRoot.Row
public import HexRCF.SelectedRoot.RowIntermediates
public import HexRCF.SelectedRoot.Collect
public import HexRealClosureMathlib.KernelReplay
public import Lean.Elab.Command

public import HexRCF.SelectedRoot.RowTools

public section

meta section
namespace Hex.RCF.SelectedRootTests.RowCollect
open Hex.RCF.SelectedRootTests
open Lean Meta Elab Command Hex Hex.RealClosure Hex.SignDet
open Hex.RealClosure.Algebraic

private def control : TermElabM Unit := do
  let simpContext ← Simp.mkContext (simpTheorems := #[← RowTools.rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let program := mkConst ``Row.rowProgram
  let mut facts := mkConst ``Collect.facts
  for index in [:13] do
    let packet := mkConst (Name.str `Hex.RCF.SelectedRootTests.RowIntermediates s!"packet{index}")
    let polynomial ← mkAppM ``Prod.fst #[packet]
    let rest ← mkAppM ``Prod.snd #[packet]
    let claimed ← mkAppM ``Prod.fst #[rest]
    let graph ← mkAppM ``Prod.snd #[rest]
    let expression := mkAppN (mkConst ``Read.fromPacket?) #[polynomial, claimed, graph]
    let some fact ← ReplayTools.readExpression (200+index) expression
      | throwError "frozen row intermediate rejected"
    facts ← mkAppM ``List.cons #[fact, facts]
  let collected ← KernelReplay.collectMany 0 program #[⟨facts⟩]
    simpContext (fun _ _ => pure none)
  match collected.outcome with
  | .checked true proof axioms =>
    let some inventory := collected.inventories[0]? | throwError "missing frozen row inventory"
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let factsName := `Hex.RCF.SelectedRootTests.RowCollect.facts
    let factType ← inferType inventory.facts
    let declaration := Declaration.defnDecl {
      name := factsName, levelParams := [], type := factType, value := inventory.facts,
      hints := .regular 0, safety := .safe }
    let env ← ofExceptKernelException <| (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    setEnv env
    compileDecl declaration (logErrors := true)
    let acceptedType ← mkEq (mkApp program (mkConst factsName)) (mkConst ``Bool.true)
    let acceptedName := `Hex.RCF.SelectedRootTests.RowCollect.rowAccepted
    let _ ← KernelReplay.auditProof proof acceptedType
    KernelCheck.addChecked acceptedName acceptedType proof
    logInfo m!"row checked: true; native unfolds=0; requests={collected.requests.size}; axioms={axioms}"
  | .checked false .. => throwError "valid joint row rejected"
  | .missing application => throwError "frozen row still demands arithmetic: {application}"

elab "#selected_row_collect" : command => liftTermElabM control
end Hex.RCF.SelectedRootTests.RowCollect
/-- info: row checked: true; native unfolds=0; requests=0; axioms=[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
#selected_row_collect

/-- info: 'Hex.RCF.SelectedRootTests.RowCollect.rowAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.SelectedRootTests.RowCollect.rowAccepted
