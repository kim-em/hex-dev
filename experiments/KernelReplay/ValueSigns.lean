/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.Packing
public meta import KernelReplay.Packing
public import HexRealClosure.ValueSigns
public meta import HexRealClosure.ValueSigns
import all HexRealClosure.ValueSigns
public import KernelReplay.Generated
public meta import KernelReplay.Generated
public import HexRealClosure.ReplayOperations
public meta import HexRealClosure.ReplayOperations
import all HexRealClosure.Packing
import all HexSignDet.DagSelectedSigns
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexRealClosure.Algebraic
import all HexPoly.Dense
import all Init.Data.Rat.Basic
import all HexRealClosureMathlib.PackingConformance
import all HexRealClosureMathlib.CoefficientSignsConformance
import all HexSignDet.Descriptor
import all HexPoly.Euclid.DivGcd
import all HexRealRoots.TarskiShared
import all HexRealClosure.ReplayOperations
import all Init.Data.Array.Basic

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.ValueSignsProbe
open Lean Meta Elab Command Hex.SignDet CoefficientSignsConformance PackingConformance

/-- Only supplied graph data enters the checked stored-value reader. -/
@[expose] def recordFromPacket? (value : Element context) (packet : Codec.Json) :
    Option (ValueSign context) := do
  let graph ← (Codec.readGraph ValueCodec.rat ValueCodec.nat 7 context.root.raw.head
    context.root.raw.lower context.root.raw.upper packet).toOption
  let memo ← graph.validate? Sturm.orderSign 7 context.root.raw.head
    context.root.raw.lower context.root.raw.upper
  ValueSign.readMemo? value memo graph.root

@[expose] def program (records : List (ValueSign context)) (value : Element context) : Bool :=
  decide (Element.replaySign records value = 1)

public meta section

/-- Native production returns graph data, never a proof object. -/
private unsafe def produce (value : Expr) : MetaM Codec.Json := do
  let polynomial ← mkAppM ``Element.polynomial #[value]
  let p ← evalExpr (DensePoly Rat) (← inferType polynomial) polynomial (checkMeta := false)
  let signs ← match context.buildSigns [p] with
    | .ok signs => pure signs
    | .error error => throwError "input-sign production failed: {reprStr error}"
  return Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode signs.evidence)

def readRecord (value : Expr) (packet : Codec.Json) : MetaM (Option Expr) := do
  let original := mkAppN (mkConst ``recordFromPacket?) #[value, KernelReplay.jsonExpr packet]
  let result ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (whnf original)
  let mut rules : SimpTheorems := {}
  for name in #[``Dag.step_eq, ``Node.check_eq, ``checkMoment_eq,
      ``TarskiCertificate.check_eq, ``Array.toList_range] do
    rules ← rules.addConst name
  rules ← rules.addConst ``Array.all_toList (inv := true)
  rules ← rules.addConst ``Array.foldlM_toList (inv := true)
  let simpContext ← Simp.mkContext (simpTheorems := #[rules])
    (config := { decide := false }) (congrTheorems := ← getSimpCongrTheorems)
  let (simplified, _) ← Meta.simp result simpContext
  let equation ← simplified.getProof' result
  let equationType ← mkEq result simplified.expr
  let _ ← KernelReplay.auditProof equation equationType
  KernelReplay.kernelCheck `__valueSignPacketRead equationType equation
  let result ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (reduce simplified.expr)
  unless result.getAppFn.isConstOf ``Option.none || result.getAppFn.isConstOf ``Option.some do
    throwError "stored-value sign reader remained at {result.getAppFn}; constants: {result.getUsedConstants.toList.filter (fun name => name.toString.startsWith "Hex" || name.toString.startsWith "Rat")}"
  let conversionType ← mkEq original result
  let _ ← KernelReplay.auditProof equation conversionType
  KernelReplay.kernelCheck `__valueSignPacket conversionType equation
  if result.getAppFn.isConstOf ``Option.none then return none
  let retained := result.getAppArgs.back!
  let reflexive ← mkEqRefl retained
  let _ ← KernelReplay.auditProof reflexive (← inferType reflexive)
  KernelReplay.kernelCheck `__valueSignRetained (← inferType reflexive) reflexive
  return some retained

private unsafe def accepted : TermElabM Unit := do
  let initial ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (ValueSign context)))) none)
  let zero ← Term.withoutErrToSorry (Term.elabTerm (← `((0 : Element context))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let initial ← instantiateMVars initial
  let zero ← instantiateMVars zero
  let simpContext ← Simp.mkContext (simpTheorems := #[])
    (congrTheorems := ← getSimpCongrTheorems)
  let mut literalInventory := initial
  for value in [zero, mkConst ``PackingConformance.literal, mkConst ``PackingConformance.small] do
    let applied ← withLocalDeclD `records (← inferType initial) fun records =>
      mkLambdaFVars #[records] (mkApp2 (mkConst ``program) records value)
    let uncovered ← collectMany 0 applied #[⟨initial⟩] simpContext (fun _ _ => pure none)
    match uncovered.outcome with
    | .missing _ => pure ()
    | _ => throwError "cached input sign bypassed its evidence boundary"
    unless uncovered.requests.size == 1 do throwError "wrong input-sign request count"
    let some needed := uncovered.requests[0]? | throwError "missing input-sign request"
    unless needed.kind == .valueSign do throwError "cached sign requested arithmetic packing"
    let some input := needed.value | throwError "cached-sign request lost its actual value"
    kernelCheck `__valueSignRequestedInput (← mkEq input value) (← mkEqRefl value)
    let polynomial ← mkAppM ``Element.polynomial #[value]
    kernelCheck `__valueSignRequestedPolynomial (← mkEq needed.polynomial polynomial)
      (← mkEqRefl polynomial)
    let packet ← produce value
    let some record ← readRecord value packet | throwError "honest input-sign packet rejected"
    let checked ← collectMany 1 applied #[⟨initial⟩] simpContext
      (fun request _ => do
        unless request.kind == .valueSign do throwError "unexpected packing demand"
        return some record)
    match checked.outcome with
    | .checked result proof _ =>
      let expected := value != zero
      unless result == expected do throwError "wrong cached input sign"
      kernelCheck `__valueSignCollected
        (← mkEq (mkAppN applied (checked.inventories.map Inventory.facts)) (toExpr result)) proof
    | _ => throwError "recorded input sign failed to replay"
    let repeated ← collectMany 0 applied checked.inventories simpContext
      (fun _ _ => throwError "cached input-sign replay called producer")
    match repeated.outcome with
    | .checked .. => pure ()
    | _ => throwError "cached input-sign record did not replay"
    unless repeated.requests.isEmpty do throwError "cached sign requested new evidence"
    if value == mkConst ``PackingConformance.literal then
      let some inventory := checked.inventories[0]? | throwError "missing input-sign inventory"
      literalInventory := inventory.facts
      unless (← readRecord (mkConst ``PackingConformance.small) packet).isNone do
        throwError "same-value polynomial mutation accepted another query"
    unless (← readRecord value .null).isNone do throwError "malformed input graph accepted"
  let smallProgram ← withLocalDeclD `records (← inferType initial) fun records =>
    mkLambdaFVars #[records] (mkApp2 (mkConst ``program) records
      (mkConst ``PackingConformance.small))
  let changed ← collectMany 0 smallProgram #[⟨literalInventory⟩] simpContext
    (fun _ _ => pure none)
  match changed.outcome with
  | .missing _ => pure ()
  | _ => throwError "stored-literal evidence covered a different same-value key"
  logInfo "three input signs kernel checked; exact value requests, cached replay and literal mutations checked"

syntax (name := valueSignPackets) "#value_sign_packets" : command
@[command_elab valueSignPackets]
unsafe def elaboratePackets : CommandElab := fun _ => liftTermElabM accepted

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
/-- info: three input signs kernel checked; exact value requests, cached replay and literal mutations checked -/
#guard_msgs in
#value_sign_packets

end Hex.RealClosure.Algebraic.KernelReplay.ValueSignsProbe
