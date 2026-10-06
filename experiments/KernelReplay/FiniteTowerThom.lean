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

/-- Omit the natural-cast and derivative-product key, retaining other records. -/
@[expose] def withoutDerivative (entries : List (Packing FiniteTower.first)) :
    List (Packing FiniteTower.first) :=
  entries.filter (fun entry => entry.original != DensePoly.C (2 : Rat))

public meta section
open Lean Meta Elab Command FiniteTowerPackets

private unsafe def derivativeControls : TermElabM Unit := withExporting (isExporting := false) do
  let subject := mkConst ``thomRaw
  let raw ← evalExpr (Hex.SignDet.RawDescriptor (Element FiniteTower.first) Nat)
    (← inferType subject) subject (checkMeta := false)
  let packet ← FiniteTowerPackets.produceRaw raw
  let assembly ← FiniteTowerPackets.collect packet ``unboundProgram
  let inventories := assembly.collection.inventories
  let supplied := inventories.map Inventory.facts
  match assembly.collection.outcome with
  | .checked true proof _ =>
    kernelCheck `__finiteTowerThom
      (← mkEq (mkAppN assembly.program supplied) (mkConst ``Bool.true)) proof
  | _ => throwError "nonempty nested Thom descriptor was not accepted"
  let key ← mkAppM ``DensePoly.C #[toExpr (2 : Rat)]
  let mut reached := false
  for needed in assembly.collection.requests do
    if needed.kind == .coefficient && (← withTransparency .all (isDefEq needed.polynomial key)) then
      reached := true
  unless reached do
    let mut keys : List String := []
    for needed in assembly.collection.requests do
      if needed.kind == .coefficient then
        let p ← evalExpr (DensePoly Rat) (← inferType needed.polynomial)
          needed.polynomial (checkMeta := false)
        keys := keys ++ [reprStr p.toArray]
    throwError "nested Thom replay did not request its derivative key; actual keys: {keys}"
  let some entries := supplied[0]? | throwError "nested Thom replay lost packing records"
  let some signs := inventories[1]? | throwError "nested Thom replay lost input signs"
  let retained := mkApp (mkConst ``withoutDerivative) entries
  let simpContext ← Simp.mkContext (simpTheorems := #[])
    (congrTheorems := ← getSimpCongrTheorems)
  let missing ← collectMany 0 assembly.program #[⟨retained⟩, signs] simpContext
    (fun _ _ => throwError "derivative omission invoked a producer")
  match missing.outcome with
  | .missing application =>
    let needed ← request application
    unless needed.kind == .coefficient && (← withTransparency .all (isDefEq needed.polynomial key)) do
      throwError "derivative omission stopped at an unrelated evidence boundary"
  | _ => throwError "nested Thom replay accepted an absent derivative record"
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
