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
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe
public meta section
open Lean Meta Elab Command FiniteTowerPackets

private unsafe def accepted : TermElabM Unit := withExporting (isExporting := false) do
  let packet ← FiniteTowerPackets.produce
  let assembly ← FiniteTowerPackets.collect packet
  let supplied := assembly.collection.inventories.map Inventory.facts
  match assembly.collection.outcome with
  | .checked true proof _ =>
    kernelCheck `__finiteTowerDescriptor
      (← mkEq (mkAppN assembly.program supplied) (mkConst ``Bool.true)) proof
  | .missing _ => throwError "nested descriptor has missing evidence after collection"
  | _ => throwError "nested descriptor was not accepted"
  let simpContext ← Simp.mkContext (simpTheorems := #[])
    (congrTheorems := ← getSimpCongrTheorems)
  let cached ← collectMany 0 assembly.program assembly.collection.inventories simpContext
    (fun _ _ => throwError "cached nested replay invoked a producer")
  match cached.outcome with
  | .checked true proof _ =>
    kernelCheck `__finiteTowerCached
      (← mkEq (mkAppN assembly.program (cached.inventories.map Inventory.facts))
        (mkConst ``Bool.true)) proof
  | _ => throwError "cached nested descriptor did not replay"
  unless cached.requests.isEmpty do throwError "cached nested replay requested new evidence"
  let entryType ← mkAppM ``Packing #[mkConst ``FiniteTower.first]
  let absent ← mkListLit entryType []
  let some inputSigns := assembly.collection.inventories[1]?
    | throwError "nested descriptor lost its input-sign inventory"
  let withoutPacking := #[⟨absent⟩, inputSigns]
  let omitted ← collectMany 0 assembly.program withoutPacking simpContext
    (fun _ _ => throwError "omission control invoked a producer")
  match omitted.outcome with
  | .missing _ => pure ()
  | _ => throwError "nested descriptor accepted without required packing records"
  logInfo m!"nested descriptor kernel checked; literals={packet.coefficients.length}, requests={assembly.collection.requests.size}; cached replay checked"

syntax (name := finiteTowerPackets) "#finite_tower_packets" : command
@[command_elab finiteTowerPackets]
unsafe def elaboratePackets : CommandElab := fun _ => liftTermElabM accepted

end

/-- info: nested descriptor kernel checked; literals=4, requests=15; cached replay checked -/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
#finite_tower_packets

end Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe
