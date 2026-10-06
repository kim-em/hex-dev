/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.KernelReplay
public meta import HexRealClosureMathlib.KernelReplay
public import HexRealClosureMathlib.PackingConformance
public meta import HexRealClosureMathlib.PackingConformance
public import KernelReplay.Packing
public meta import KernelReplay.Packing
import all HexRealClosure.Packing
import all HexRealClosure.ReplayOperations
import all HexRealClosure.Algebraic
import all HexRealClosureMathlib.PackingConformance
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexSignDet.Descriptor
import all HexPoly.Euclid.DivGcd
import all HexPoly.Dense
import all HexRealRoots.TarskiShared
import all Init.Data.Array.Basic

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.PackingProbe

open CoefficientSignsConformance PackingConformance

@[expose] def program (entries : List (Algebraic.Packing context)) (p : DensePoly Rat) : Bool :=
  decide ((Element.replayPack entries p).sign = 0)

@[expose] def legacy (facts : List (SignFact context)) : Bool :=
  decide ((Element.pack reduction reduction_eq facts 0).sign = 0)

/-- Each operation follows the actual native polynomial operation and routes
its packing through the complete original-key inventory. -/
@[expose] def operation (entries : List (Algebraic.Packing context)) (index : Nat) : Bool :=
  let a : Element context := small
  let result := match index with
    | 0 => (Element.replayAdd inferInstance rfl entries).add a 0
    | 1 => (Element.replaySub inferInstance rfl entries).sub a a
    | 2 => (Element.replayMul inferInstance inferInstance rfl rfl entries).mul a a
    | 3 => (Element.replayNeg inferInstance rfl entries).neg a
    | 4 => (Element.replayOne inferInstance rfl entries).one
    | 5 => (Element.replayNatCast inferInstance rfl entries).natCast 3
    | 6 => (Element.replayInv inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance rfl rfl rfl rfl rfl rfl entries).inv a
    | _ => (Element.replayDiv inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance rfl rfl rfl rfl rfl rfl entries).div a a
  decide (result.sign = 0)

public meta section

open Lean Meta Elab Command

syntax "#packing_requests" : command
elab_rules : command
| `(#packing_requests) => liftTermElabM do
  let initial ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (Algebraic.Packing context)))) none)
  let scalarInitial ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (SignFact context)))) none)
  let inputs ← #[
    (← Term.withoutErrToSorry (Term.elabTerm (← `((0 : DensePoly Rat))) none)),
    (← Term.withoutErrToSorry (Term.elabTerm (← `((DensePoly.C 1 : DensePoly Rat))) none)),
    (← Term.withoutErrToSorry (Term.elabTerm (← `((Sturm.Fixtures.p : DensePoly Rat))) none))].mapM
      instantiateMVars
  Term.synthesizeSyntheticMVarsNoPostponing
  let initial ← instantiateMVars initial
  let scalarInitial ← instantiateMVars scalarInitial
  let simpContext ← Simp.mkContext (simpTheorems := #[])
    (congrTheorems := ← getSimpCongrTheorems)
  let old ← collectMany 0 (mkConst ``legacy) #[⟨scalarInitial⟩] simpContext
    (fun _ _ => pure none)
  match old.outcome with
  | .checked true .. => pure ()
  | _ => throwError "legacy constant packing should need no supplied fact"
  unless old.requests.isEmpty do throwError "unexpected legacy constant request"
  for input in inputs do
    let applied ← withLocalDeclD `entries (← inferType initial) fun entries => do
      mkLambdaFVars #[entries] (mkApp2 (mkConst ``program) entries input)
    let collected ← collectMany 0 applied #[⟨initial⟩] simpContext (fun _ _ => pure none)
    match collected.outcome with
    | .missing _ => pure ()
    | _ => throwError "unrecorded raw packing reached a Boolean result"
    unless collected.requests.size == 1 do throwError "missing original packing request"
    let some needed := collected.requests[0]? |
      throwError "missing original packing request"
    let actualContext := mkConst ``CoefficientSignsConformance.context
    kernelCheck `__packingRequestContext (← mkEq needed.context actualContext)
      (← mkEqRefl actualContext)
    kernelCheck `__packingRequestOriginal (← mkEq needed.polynomial input) (← mkEqRefl input)
  for i in [:8] do
    let applied ← withLocalDeclD `entries (← inferType initial) fun entries =>
      mkLambdaFVars #[entries] (mkApp2 (mkConst ``operation) entries (toExpr i))
    let collected ← collectMany 0 applied #[⟨initial⟩] simpContext (fun _ _ => pure none)
    match collected.outcome with
    | .missing _ => pure ()
    | _ => throwError "operation {i} bypassed original packing evidence"
    unless collected.requests.size == 1 do throwError "wrong operation request count"
  logInfo "constant zero, constant one and original head require exact raw packing records"

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
/-- info: constant zero, constant one and original head require exact raw packing records -/
#guard_msgs in
#packing_requests

public meta section

open Lean Meta Elab Command

private unsafe def accepted : TermElabM Unit := do
  let initial ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (Algebraic.Packing context)))) none)
  let scalarInitial ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (SignFact context)))) none)
  let inputs ← #[
    (← Term.withoutErrToSorry (Term.elabTerm (← `((0 : DensePoly Rat))) none)),
    (← Term.withoutErrToSorry (Term.elabTerm (← `((DensePoly.C 1 : DensePoly Rat))) none)),
    (← Term.withoutErrToSorry (Term.elabTerm (← `((Sturm.Fixtures.p : DensePoly Rat))) none))].mapM
      instantiateMVars
  Term.synthesizeSyntheticMVarsNoPostponing
  let initial ← instantiateMVars initial
  let scalarInitial ← instantiateMVars scalarInitial
  let simpContext ← Simp.mkContext (simpTheorems := #[])
    (congrTheorems := ← getSimpCongrTheorems)
  let mut packets : List Packing.Packet := []
  let mut zeroInventory := initial
  for i in [:inputs.size] do
    let input := inputs[i]!
    let some packet ← Packing.produce { context := mkConst ``CoefficientSignsConformance.context, polynomial := input } |
      throwError "packing packet production failed"
    packets := packet :: packets
    let applied ← withLocalDeclD `scalars (← inferType scalarInitial) fun scalars => do
      withLocalDeclD `entries (← inferType initial) fun entries => do
        mkLambdaFVars #[scalars, entries] (mkApp2 (mkConst ``program) entries input)
    let collected ← collectMany 1 applied #[⟨scalarInitial⟩, ⟨initial⟩] simpContext
      (fun needed _ => do
        let record ← Packing.readPackets [packet] needed
        unless record.isSome do
          throwError "packing packet {i} reader rejected request {needed.polynomial}"
        return record)
    match collected.outcome with
    | .checked value proof _ =>
      unless value == (i != 1) do throwError "wrong packed sign"
      kernelCheck `__packingAccepted
        (← mkEq (mkAppN applied (collected.inventories.map Inventory.facts)) (toExpr value)) proof
    | .missing application =>
      throwError "packing packet {i} left a missing application {application}"
    unless collected.requests.size == 1 do throwError "wrong original request count"
    let some scalars := collected.inventories[0]? | throwError "missing scalar inventory"
    let some entries := collected.inventories[1]? | throwError "missing packing inventory"
    kernelCheck `__packingMixedInventory (← mkEq scalars.facts scalarInitial)
      (← mkEqRefl scalarInitial)
    let replayed ← collectMany 0 applied collected.inventories simpContext
      (fun _ _ => throwError "cached replay called supplier")
    match replayed.outcome with
    | .checked .. => pure ()
    | _ => throwError "cached record did not replay"
    unless replayed.requests.isEmpty do throwError "cached record produced a new request"
    if i == 0 then zeroInventory := entries.facts
    if i == 2 then
      let rawZero ← withLocalDeclD `entries (← inferType initial) fun entries =>
        mkLambdaFVars #[entries] (mkApp2 (mkConst ``program) entries input)
      let uncovered ← collectMany 0 rawZero #[⟨zeroInventory⟩] simpContext
        (fun _ _ => pure none)
      match uncovered.outcome with
      | .missing _ => pure ()
      | _ => throwError "different raw zero equation reused one packing record"
      unless (← Packing.readRecord { packet with original := (Hex.SignDet.Codec.poly
          Hex.SignDet.ValueCodec.rat (0 : DensePoly Rat)) }).isNone do
        throwError "same-value original mutation accepted another joint replay"
  unless packets.length == 3 do throwError "missing retained packets"
  let zeroProgram ← withLocalDeclD `entries (← inferType initial) fun entries =>
    mkLambdaFVars #[entries] (mkApp2 (mkConst ``program) entries inputs[0]!)
  let wrongKind : Except Exception Collections ← try
    let result ← collectMany 1 zeroProgram #[⟨initial⟩] simpContext (fun _ _ => do
      let scalar ← mkAppM ``List.head? #[mkConst ``PackingConformance.facts]
      let scalar ← withTransparency .all (whnf scalar)
      unless scalar.getAppFn.isConstOf ``Option.some do throwError "missing scalar fixture"
      return some scalar.getAppArgs.back!)
    pure (.ok result)
  catch error => pure (.error error)
  match wrongKind with
  | .error error =>
    unless (← error.toMessageData.toString) ==
        "supplied fact belongs to a different inventory kind" do throw error
  | .ok _ => throwError "scalar fact accepted as a complete packing record"
  let divide ← withLocalDeclD `entries (← inferType initial) fun entries =>
    mkLambdaFVars #[entries] (mkApp2 (mkConst ``operation) entries (toExpr (7 : Nat)))
  let divisionPackets ← IO.mkRef ([] : List Packing.Packet)
  let divided ← collectMany 3 divide #[⟨initial⟩] simpContext (fun needed _ => do
    let some packet ← Packing.produce needed | return none
    divisionPackets.modify (packet :: ·)
    let record ← Packing.readPackets [packet] needed
    unless record.isSome do throwError "division packet did not match {needed.polynomial}"
    return record)
  match divided.outcome with
  | .checked false proof _ =>
    kernelCheck `__packingDivision
      (← mkEq (mkAppN divide (divided.inventories.map Inventory.facts)) (mkConst ``Bool.false)) proof
  | .checked true .. => throwError "native nonzero division returned zero"
  | .missing application =>
    throwError "division retained {divided.requests.size} requests but still needs {application}"
  unless divided.requests.size == 2 do throwError "division did not retain inverse and product"
  let some first := divided.requests[0]? | throwError "missing inverse request"
  let some second := divided.requests[1]? | throwError "missing product request"
  kernelCheck `__packingDivisionInverse (← mkEq first.polynomial (mkConst ``inverseKey))
    (← mkEqRefl (mkConst ``inverseKey))
  let square ← Term.withoutErrToSorry
    (Term.elabTerm (← `((Sturm.Fixtures.x * Sturm.Fixtures.x : DensePoly Rat))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let square ← instantiateMVars square
  kernelCheck `__packingDivisionProduct (← mkEq second.polynomial square) (← mkEqRefl square)
  let dividedAgain ← collectMany 0 divide divided.inventories simpContext
    (fun _ _ => throwError "cached division called supplier")
  match dividedAgain.outcome with
  | .checked false .. => pure ()
  | _ => throwError "cached division did not replay"
  unless dividedAgain.requests.isEmpty do throwError "cached division requested another record"
  logInfo "three raw packets kernel checked; mixed inventories, cached replay and distinct zero equations checked"

syntax (name := packingAccepted) "#packing_accepted" : command
@[command_elab packingAccepted]
unsafe def elaborateAccepted : CommandElab := fun _ => liftTermElabM accepted

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
/-- info: three raw packets kernel checked; mixed inventories, cached replay and distinct zero equations checked -/
#guard_msgs in
#packing_accepted

end Hex.RealClosure.Algebraic.KernelReplay.PackingProbe
