/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

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
import all HexSignDet.Descriptor
import all HexPoly.Euclid.DivGcd
import all Init.Data.Array.Basic

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.Packing

open Lean Meta Hex.SignDet CoefficientSignsConformance PackingConformance

/-- Read both scalar packing evidence and the joint raw-equation evidence.
Both graph packets are supplied; production is absent from this reader. -/
@[expose] def recordFromPackets? (original : Codec.Json) (retained : Codec.Json)
    (claimed : Int) (scalar joint : Codec.Json) : Option (Algebraic.Packing context) := do
  let p ← (Codec.readPoly ValueCodec.rat original).toOption
  let fact ← Generated.factFromPackets? retained claimed scalar
  let graph ← (Codec.readGraph ValueCodec.rat ValueCodec.nat 7 context.root.raw.head
    context.root.raw.lower context.root.raw.upper joint).toOption
  let memo ← graph.validate? Sturm.orderSign 7 context.root.raw.head
    context.root.raw.lower context.root.raw.upper
  Algebraic.Packing.readMemo? reduction reduction_eq [fact] p memo graph.root

meta section

structure Packet where
  original : Codec.Json
  scalar : Generated.Packet
  joint : Codec.Json

/-- Produce literal packets for the exact original request. Even a constant
or zero output retains its own joint selected-root replay. No native proof
object crosses from production into ordinary-kernel checking. -/
unsafe def produce (needed : Request) : MetaM (Option Packet) := do
  unless ← isDefEq needed.context (mkConst ``CoefficientSignsConformance.context) do
    return none
  let expected ← mkAppOptM ``DensePoly #[some (mkConst ``Rat), none, none]
  let p ← evalExpr (DensePoly Rat) expected needed.polynomial (checkMeta := false)
  let kept := reduction p
  let scalar ← match context.buildSigns [context.queryPoly kept] with
    | .ok signs => pure signs
    | .error error => throwError "scalar packing production failed: {reprStr error}"
  let joint ← match context.buildSigns [kept, p - kept] with
    | .ok signs => pure signs
    | .error error => throwError "joint packing production failed: {reprStr error}"
  let packet : Packet := ⟨Codec.poly ValueCodec.rat p,
    ⟨Codec.poly ValueCodec.rat kept, scalar.value,
      Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode scalar.evidence)⟩,
    Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode joint.evidence)⟩
  return some packet

/-- Reduce and audit only the supplied finite packets. The equality of the
reader result and every returned record are checked by the ordinary kernel. -/
def readRecord (packet : Packet) : MetaM (Option Expr) := do
  let original := mkAppN (mkConst ``recordFromPackets?)
    #[KernelReplay.jsonExpr packet.original, KernelReplay.jsonExpr packet.scalar.polynomial,
      toExpr packet.scalar.claimed, KernelReplay.jsonExpr packet.scalar.graph,
      KernelReplay.jsonExpr packet.joint]
  let result ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (whnf original)
  let mut rules : SimpTheorems := {}
  for name in #[``Dag.step_eq, ``Node.check_eq, ``checkMoment_eq,
      ``TarskiCertificate.check_eq, ``Array.toList_range] do
    rules ← rules.addConst name
  rules ← rules.addConst ``Array.all_toList (inv := true)
  rules ← rules.addConst ``Array.foldlM_toList (inv := true)
  let simpContext ← Simp.mkContext (simpTheorems := #[rules])
    (config := { decide := false })
    (congrTheorems := ← getSimpCongrTheorems)
  let (simplified, _) ← Meta.simp result simpContext
  let equation ← simplified.getProof' result
  let equationType ← mkEq result simplified.expr
  let _ ← KernelReplay.auditProof equation equationType
  KernelReplay.kernelCheck `__packingPacketRead equationType equation
  let result ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (reduce simplified.expr)
  unless result.getAppFn.isConstOf ``Option.none || result.getAppFn.isConstOf ``Option.some do
    throwError "supplied packing record did not reduce at {result.getAppFn}"
  -- Kernel conversion checks both reductions against the original reader.
  -- Keeping the simplifier proof avoids asking metavariable unification to
  -- unfold the large literal record and all of its dependent proof fields.
  let converted := equation
  let conversionType ← mkEq original result
  let _ ← KernelReplay.auditProof converted conversionType
  KernelReplay.kernelCheck `__packingPacket conversionType converted
  if result.getAppFn.isConstOf ``Option.none then return none
  let record := result.getAppArgs.back!
  let type ← mkEq record record
  let proof ← mkEqRefl record
  let _ ← KernelReplay.auditProof proof type
  KernelReplay.kernelCheck `__packingRecord type proof
  return some record

/-- Match a supplied packet by its original key, then use the strict reader.
A record for a reduced representative cannot satisfy a different raw request. -/
def readPackets (packets : List Packet) (needed : Request) : MetaM (Option Expr) := do
  unless ← isDefEq needed.context (mkConst ``CoefficientSignsConformance.context) do
    return none
  for packet in packets do
    let decoded ← mkAppM ``Codec.readPoly
      #[mkConst ``ValueCodec.rat, KernelReplay.jsonExpr packet.original]
    let decoded ← withTransparency .all (reduce decoded)
    unless decoded.getAppFn.isConstOf ``Except.ok do continue
    let polynomial := decoded.getAppArgs.back!
    let type ← mkEq needed.polynomial polynomial
    let proof ← mkEqRefl polynomial
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let matched := (← getEnv).toKernelEnv.addDecl options
      (.thmDecl { name := `__packingPacketKey, levelParams := [], type, value := proof })
    if ← KernelReplay.acceptKernel matched then return ← readRecord packet
  return none

end

end Hex.RealClosure.Algebraic.KernelReplay.Packing
