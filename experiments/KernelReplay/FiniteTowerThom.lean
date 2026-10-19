/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteTowerPackets
public meta import KernelReplay.FiniteTowerPackets
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns
import all HexRealClosure.PackingReplay
import all HexRealClosure.SignCodec
import all HexRealClosure.SignRequests
import all HexRealClosure.Algebraic
import all HexSignDet.Descriptor
import all HexSignDet.Dag
import all HexSignDet.Thom
import all HexSignDet.Replay
import all HexSignDet.MomentReplay
import all HexSignDet.QueryReduction
import all HexSignDet.Reduction
import all HexSignDet.Matrix
import all HexRank.Cert
import all HexMatrix.MatrixAlgebra
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexSignDet.Codec.Coefficients
import all HexRealRoots.TarskiShared
import all HexPoly.Dense
import all HexPoly.Euclid.DivGcd
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic
import all Init.Prelude

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerThom

/-- Select the positive root by its first derivative over the whole real line.
Unlike the bounded subject, this literal subject forces a nonempty Thom query. -/
@[expose] def thomRaw : Hex.SignDet.RawDescriptor (Element FiniteTower.first) Nat :=
  ⟨8, FiniteTower.nextRaw.head, .negInf, .posInf, [1], [1]⟩

/-- Bind the whole-line subject to the independently requested positive Thom word. -/
@[expose] def thomRequested (entries : List (Packing FiniteTower.first)) :
    Hex.SignDet.RawDescriptor (Element FiniteTower.first) Nat :=
  ⟨8, (FiniteTower.requestedRaw entries).head, .negInf, .posInf, [1], [1]⟩

@[expose] def thomProgram (facts : List (SignFact FiniteTower.first))
    (subject packet : Hex.SignDet.Codec.Json) (entries : List (Packing FiniteTower.first))
    (signs : List (ValueSign FiniteTower.first)) : Bool :=
  match FiniteTower.readUnbound? facts entries signs subject packet with
  | none => false
  | some root => decide (root.raw = thomRequested entries)

/-- Force the actual first derivative coefficient through the supplied query
operations, independently of every graph and squarefree check. -/
@[expose] def queryProgram (entries : List (Packing FiniteTower.first)) : Bool :=
  let qs := @Hex.SignDet.RawDescriptor.queries (Element FiniteTower.first) Nat _ _
    (Element.replayNatCast (inferInstance : NatCast Rat) rfl entries)
    (Element.replayMul (inferInstance : Add Rat) (inferInstance : Mul Rat) rfl rfl entries) thomRaw
  match qs with
  | [q] => (q.coeff 1).polynomial == DensePoly.C (2 : Rat)
  | _ => false

@[expose] def derivativeKey (p : DensePoly Rat) : Bool := p == DensePoly.C (2 : Rat)

/-- Omit the constant two key, retaining every other packing record. -/
@[expose] def withoutDerivative (entries : List (Packing FiniteTower.first)) :
    List (Packing FiniteTower.first) := entries.filter (fun entry => !derivativeKey entry.original)

public meta section
open Lean Meta Elab Command FiniteTowerPackets

private unsafe def derivativeControls : TermElabM Unit := withExporting (isExporting := false) do
  let subject := mkConst ``thomRaw
  let raw ← evalExpr (Hex.SignDet.RawDescriptor (Element FiniteTower.first) Nat)
    (← inferType subject) subject (checkMeta := false)
  let packet ← FiniteTowerPackets.produceRaw raw
  let assembly ← FiniteTowerPackets.collect packet ``thomProgram
  let inventories := assembly.collection.inventories
  let supplied := inventories.map Inventory.facts
  match assembly.collection.outcome with
  | .checked true proof _ =>
    kernelCheck `__finiteTowerThom
      (← mkEq (mkAppN assembly.program supplied) (mkConst ``Bool.true)) proof
  | _ => throwError "nonempty nested Thom descriptor was not accepted"
  let some entries := supplied[0]? | throwError "nested Thom replay lost packing records"
  let query := mkConst ``queryProgram
  let simpContext ← Simp.mkContext (simpTheorems := #[])
    (congrTheorems := ← getSimpCongrTheorems)
  let checked ← collectMany 0 query #[⟨entries⟩] simpContext
    (fun _ _ => throwError "query replay invoked a producer")
  match checked.outcome with
  | .checked true proof _ =>
    kernelCheck `__finiteTowerDerivative
      (← mkEq (mkApp query entries) (mkConst ``Bool.true)) proof
  | _ => throwError "first derivative query did not match its exact coefficient"
  let retained := mkApp (mkConst ``withoutDerivative) entries
  let missing ← collectMany 0 query #[⟨retained⟩] simpContext
    (fun _ _ => throwError "derivative omission invoked a producer")
  match missing.outcome with
  | .missing application =>
    let needed ← request application
    unless needed.kind == .coefficient do
      throwError "derivative query stopped at a different kind of evidence"
    kernelCheck `__finiteTowerDerivativeKey
      (← mkEq (mkApp (mkConst ``derivativeKey) needed.polynomial) (mkConst ``Bool.true))
      (← mkEqRefl (mkConst ``Bool.true))
  | _ => throwError "derivative query accepted an absent constant two record"
  let noRoot := { raw with signs := [0] }
  let rejectedPacket : FiniteTowerPackets.Packet :=
    ⟨SignRequests.binding (Element.codec Hex.SignDet.ValueCodec.rat)
      Hex.SignDet.ValueCodec.nat noRoot, packet.graph, packet.coefficients⟩
  let rejected ← FiniteTowerPackets.collect rejectedPacket ``unboundProgram
  match rejected.collection.outcome with
  | .checked false proof _ =>
    kernelCheck `__finiteTowerThomZeroCount
      (← mkEq (mkAppN rejected.program (rejected.collection.inventories.map Inventory.facts))
        (mkConst ``Bool.false)) proof
  | _ => throwError "zero-count Thom word was accepted"
  logInfo "nonempty nested Thom queries and derivative omission kernel checked"

syntax (name := finiteTowerThom) "#finite_tower_thom" : command
@[command_elab finiteTowerThom]
unsafe def elaborateThom : CommandElab := fun _ => liftTermElabM derivativeControls

end

/-- info: nonempty nested Thom queries and derivative omission kernel checked -/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
#finite_tower_thom

end Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerThom
