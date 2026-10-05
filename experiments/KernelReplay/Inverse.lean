/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.Packing
public meta import KernelReplay.Packing
public import HexRealClosure.InversePacking
public meta import HexRealClosure.InversePacking
import all HexRealClosure.InversePacking
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

namespace Hex.RealClosure.Algebraic.KernelReplay.InverseProbe

open Lean Meta Elab Command Hex.SignDet CoefficientSignsConformance PackingConformance

/-- Read literal packing and inverse-equation graphs. The original argument is
already a checked native value; production is absent from this reader. -/
@[expose] def recordFromPacket? (argument : Element context)
    (entry : Algebraic.Packing context) (inverse : Codec.Json) :
    Option (Algebraic.Packing.Inverse entry) := do
  let graph ← (Codec.readGraph ValueCodec.rat ValueCodec.nat 7 context.root.raw.head
    context.root.raw.lower context.root.raw.upper inverse).toOption
  let memo ← graph.validate? Sturm.orderSign 7 context.root.raw.head
    context.root.raw.lower context.root.raw.upper
  Algebraic.Packing.Inverse.readMemo? argument entry memo graph.root

public meta section

structure Packet where
  packing : Packing.Packet
  inverse : Codec.Json

/-- The fixture producer exports literal data only. -/
unsafe def produce : MetaM Packet := do
  let p := inverseKey
  let kept := reduction p
  let some packing ← Packing.produce
    ⟨mkConst ``CoefficientSignsConformance.context, mkConst ``PackingConformance.inverseKey⟩
    | throwError "inverse packing data production failed"
  let some entry := Algebraic.Packing.build? reduction reduction_eq
    [⟨kept, context.signPoly kept, rfl⟩] p | throwError "inverse packing failed"
  let inverse ← match Algebraic.Packing.Inverse.build? small entry with
    | .ok record => pure record
    | .error error => throwError "inverse equation production failed: {reprStr error}"
  return ⟨packing,
    Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode inverse.signs.evidence)⟩


/-- Ordinary-kernel conversion checks acceptance or rejection of supplied
literal packets, then audits every retained dependent record. -/
def readRecord (argument : Expr) (packet : Packet) : MetaM (Option Expr) := do
  let some entry ← Packing.readRecord packet.packing | return none
  let original := mkAppN (mkConst ``recordFromPacket?)
    #[argument, entry, KernelReplay.jsonExpr packet.inverse]
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
  KernelReplay.kernelCheck `__inversePacketRead equationType equation
  let result ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (reduce simplified.expr (explicitOnly := false) (skipTypes := false))
  unless result.getAppFn.isConstOf ``Option.none || result.getAppFn.isConstOf ``Option.some do
    throwError "inverse packet reader remained at {result.getAppFn}; constants: {result.getUsedConstants.toList.filter (fun name => name.toString.startsWith "Hex" || name.toString.startsWith "Rat")}"
  let conversionType ← mkEq original result
  let _ ← KernelReplay.auditProof equation conversionType
  KernelReplay.kernelCheck `__inversePacket conversionType equation
  if result.getAppFn.isConstOf ``Option.none then return none
  let retained := result.getAppArgs.back!
  let reflexive ← mkEqRefl retained
  let _ ← KernelReplay.auditProof reflexive (← inferType reflexive)
  KernelReplay.kernelCheck `__inverseRetained (← inferType reflexive) reflexive
  return some retained

private unsafe def accepted : TermElabM Unit := do
  let packet ← produce
  let argument := mkConst ``PackingConformance.small
  let some retained ← readRecord argument packet | throwError "valid inverse packet rejected"
  let proof ← mkAppM ``Algebraic.Packing.Inverse.native #[retained]
  let _ ← KernelReplay.auditProof proof (← inferType proof)
  KernelReplay.kernelCheck `__inverseNative (← inferType proof) proof
  unless (← readRecord argument packet).isSome do throwError "supplied cached packet failed"
  let zero ← Term.withoutErrToSorry
    (Term.elabTerm (← `((0 : Element context))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let zero ← instantiateMVars zero
  unless (← readRecord zero packet).isNone do throwError "zero used a nonzero inverse packet"
  unless (← readRecord argument { packet with inverse := .null }).isNone do
    throwError "malformed inverse graph accepted"
  unless (← readRecord argument { packet with packing :=
      { packet.packing with scalar := { packet.packing.scalar with claimed := 0 } } }).isNone do
    throwError "changed packed sign accepted"
  logInfo "inverse packets retain native equality; cached replay and three mutations kernel checked"

syntax (name := inversePackets) "#inverse_packets" : command
@[command_elab inversePackets]
unsafe def elaboratePackets : CommandElab := fun _ => liftTermElabM accepted

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
/-- info: inverse packets retain native equality; cached replay and three mutations kernel checked -/
#guard_msgs in
#inverse_packets

end Hex.RealClosure.Algebraic.KernelReplay.InverseProbe
