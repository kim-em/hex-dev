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
    let statement ← mkEq (mkAppN assembly.program supplied) (mkConst ``Bool.true)
    kernelCheck `__finiteTowerDescriptor statement proof
    addDecl (.thmDecl { name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedAccepted, levelParams := [], type := statement, value := proof })
    let arguments := assembly.program.getAppArgs
    let some facts := arguments[0]? | throwError "nested reader lost its scalar facts"
    let some subject := arguments[1]? | throwError "nested reader lost its subject"
    let some graph := arguments[2]? | throwError "nested reader lost its graph"
    let some entries := supplied[0]? | throwError "nested reader lost its packing records"
    let some signs := supplied[1]? | throwError "nested reader lost its input-sign records"
    let reader := mkAppN (mkConst ``FiniteTower.readNext?) #[facts, entries, signs, subject, graph]
    let acceptedProof := mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedAccepted
    let root ← mkAppM ``Option.get #[reader, acceptedProof]
    let rootType ← inferType root
    addDecl (.defnDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedRoot
      levelParams := [], type := rootType, value := root, hints := .abbrev, safety := .safe })
    let rawProof ← mkAppM ``FiniteTower.readNext?_get_raw
      #[facts, entries, signs, subject, graph, acceptedProof]
    let rawStatement ← mkEq
      (← mkAppM ``Hex.SignDet.Descriptor.raw
        #[mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedRoot])
      (mkConst ``FiniteTower.nextRaw)
    kernelCheck `__finiteTowerSubject rawStatement rawProof
    addDecl (.thmDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedRoot_raw
      levelParams := [], type := rawStatement, value := rawProof })
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
  let signType ← mkAppM ``ValueSign #[mkConst ``FiniteTower.first]
  let absentSigns ← mkListLit signType []
  let some packed := assembly.collection.inventories[0]?
    | throwError "nested descriptor lost its packing inventory"
  let withoutSigns ← collectMany 0 assembly.program #[packed, ⟨absentSigns⟩] simpContext
    (fun _ _ => throwError "sign omission control invoked a producer")
  match withoutSigns.outcome with
  | .missing _ => pure ()
  | _ => throwError "nested descriptor accepted without required input-sign records"
  let wrong ← FiniteTowerPackets.produceRaw
    { FiniteTower.nextRaw with lower := .finite (-2), upper := .finite (-1) }
  let rejected ← FiniteTowerPackets.collect wrong
  match rejected.collection.outcome with
  | .checked false proof _ =>
    kernelCheck `__finiteTowerWrongRoot
      (← mkEq (mkAppN rejected.program (rejected.collection.inventories.map Inventory.facts))
        (mkConst ``Bool.false)) proof
  | _ => throwError "different valid selected root was not rejected by the subject binding"
  let packingCount := (assembly.collection.requests.filter (·.kind == .coefficient)).size
  let signCount := (assembly.collection.requests.filter (·.kind == .valueSign)).size
  logInfo m!"nested descriptor kernel checked; literals={packet.coefficients.length}, requests={assembly.collection.requests.size}, packing={packingCount}, signs={signCount}; cached replay and mutation controls checked"

syntax (name := finiteTowerPackets) "#finite_tower_packets" : command
@[command_elab finiteTowerPackets]
unsafe def elaboratePackets : CommandElab := fun _ => liftTermElabM accepted

end

/-- info: nested descriptor kernel checked; literals=4, requests=15, packing=9, signs=6; cached replay and mutation controls checked -/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
#finite_tower_packets

end Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedAccepted

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedRoot

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedRoot_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedRoot_raw
