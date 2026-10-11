/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteTowerPackets
public meta import KernelReplay.FiniteTowerPackets
public meta import HexRealClosureMathlib.NativeFactory
import all HexRealClosure.InversePacking
import all HexRealClosure.Algebraic

import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexSignDet.Descriptor
import all HexRealRoots.TarskiShared
import all HexPoly.Dense
import all HexPoly.Euclid.DivGcd
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns
import all HexRealClosure.RecordPackets
import all HexRealClosure.InversePackets
import all HexSignDet.Dag
import all HexSignDet.Thom
import all HexSignDet.Replay
import all HexSignDet.MomentReplay
import all HexSignDet.QueryReduction
import all HexSignDet.Reduction
import all HexSignDet.Matrix
import all HexRank.Cert
import all HexMatrix.MatrixAlgebra

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.NativeFactoryProbe
open Lean Meta Elab Command Hex.SignDet FiniteData FiniteTower

syntax (name := nativeFactoryProbe) "#native_factory_probe" : command
@[command_elab nativeFactoryProbe]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let owner := mkConst ``first
  let value := mkConst ``ValueCodec.rat
  let ctx := mkConst ``ValueCodec.nat
  let retained : NativeOwner := ⟨owner, value, ctx, mkConst ``reduction,
    mkConst ``reduction_eq, fun polynomial claimed packet =>
      mkAppM ``RationalRoot.readFact? #[owner, polynomial, claimed, packet]⟩
  let factory : NativeFactory := ⟨#[retained]⟩
  let packet ← FiniteTowerPackets.produce
  let facts ← FiniteTowerPackets.inputFacts packet
  let program := mkAppN (mkConst ``FiniteTowerPackets.program)
    #[facts, jsonExpr packet.subject, jsonExpr packet.graph]
  let entries ← mkListLit (← mkAppM ``Packing #[owner]) []
  let signs ← mkListLit (← mkAppM ``ValueSign #[owner]) []
  let simpContext ← Simp.mkContext (simpTheorems := #[])
    (congrTheorems := ← getSimpCongrTheorems)
  let collected ← collectMany 500 program #[⟨entries⟩, ⟨signs⟩] simpContext factory.supply
  match collected.outcome with
  | .checked true proof _ =>
    kernelCheck `__nativeFactoryNestedRoot
      (← mkEq (mkAppN program (collected.inventories.map Inventory.facts))
        (mkConst ``Bool.true)) proof
  | _ => throwError "native factory did not check the actual nested descriptor"
  let inverse ← factory.inverse retained (mkConst ``generator)
  let operand ← mkAppM ``Packing.Inverse.argument
    #[← mkAppM ``InverseFact.inverse #[inverse]]
  let equation ← mkEq operand (mkConst ``generator)
  let proof ← mkEqRefl (mkConst ``generator)
  let _ ← auditProof proof equation
  kernelCheck `__nativeFactoryInverseOperand equation proof
  let absent : NativeFactory := ⟨#[]⟩
  let missing ← absent.supply { context := owner, polynomial := mkConst ``variablePoly } #[]
  unless missing.isNone do throwError "native factory supplied an unregistered owner"
  let wrongReader : NativeOwner :=
    { retained with scalarReader := (fun _ _ _ => mkAppM ``Option.some #[mkConst ``generatorFact]) }
  let unit ← mkAppM ``DensePoly.C #[toExpr (1 : Rat)]
  let rejected ← try
    let _ ← factory.scalar wrongReader unit
    pure false
  catch error =>
    unless (← error.toMessageData.toString) ==
        "native scalar reader changed its original request" do throw error
    pure true
  unless rejected do throwError "native factory accepted a callback for a different polynomial"
  logInfo m!"native factory independently checked nested descriptor with {collected.requests.size} demanded records and the original generator inverse; missing owners rejected"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
#native_factory_probe

end Hex.RealClosure.Algebraic.KernelReplay.NativeFactoryProbe
