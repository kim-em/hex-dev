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

@[expose] def bindingKey (p : DensePoly Rat) : Bool :=
  p == 0 - FiniteTower.generator.polynomial || p == DensePoly.C (1 : Rat) ||
    p == DensePoly.C (2 : Rat)

@[expose] def bindingEntries (entries : List (Packing FiniteTower.first)) :
    List (Packing FiniteTower.first) := entries.filter (fun entry => bindingKey entry.original)

public meta section
open Lean Meta Elab Command FiniteTowerPackets

private def retainData (name : Name) (value : Expr) : MetaM Unit := do
  let declaration := Declaration.defnDecl {
    name, levelParams := [], type := ← inferType value, value, hints := .abbrev, safety := .safe }
  addDecl declaration (forceExpose := true)
  compileDecl declaration

private unsafe def accepted : TermElabM Unit := withExporting (isExporting := false) do
  let packet ← FiniteTowerPackets.produce
  let assembly ← FiniteTowerPackets.collect packet
  let supplied := assembly.collection.inventories.map Inventory.facts
  match assembly.collection.outcome with
  | .checked true proof _ =>
    let arguments := assembly.program.getAppArgs
    let some facts := arguments[0]? | throwError "nested reader lost its scalar facts"
    let some subject := arguments[1]? | throwError "nested reader lost its subject"
    let some graph := arguments[2]? | throwError "nested reader lost its graph"
    let some entries := supplied[0]? | throwError "nested reader lost its packing records"
    let some signs := supplied[1]? | throwError "nested reader lost its input-sign records"
    retainData `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedFacts facts
    retainData `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedEntries entries
    retainData `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedSigns signs
    retainData `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedSubject subject
    retainData `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedGraph graph
    let facts := mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedFacts
    let entries := mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedEntries
    let signs := mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedSigns
    let subject := mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedSubject
    let graph := mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedGraph
    let program := mkAppN (mkConst ``FiniteTowerPackets.program) #[facts, subject, graph]
    let statement ← mkEq (mkAppN program #[entries, signs]) (mkConst ``Bool.true)
    kernelCheck `__finiteTowerDescriptor statement proof
    addDecl (.thmDecl { name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedAccepted, levelParams := [], type := statement, value := proof })
    let reader := mkAppN (mkConst ``FiniteTower.readNext?) #[facts, entries, signs, subject, graph]
    let acceptedProof := mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedAccepted
    let root ← mkAppM ``Option.get #[reader, acceptedProof]
    let rootType ← inferType root
    let rootDeclaration := Declaration.defnDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedRoot
      levelParams := [], type := rootType, value := root, hints := .abbrev, safety := .safe }
    addDecl rootDeclaration (forceExpose := true)
    compileDecl rootDeclaration
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
  let packingCount := (assembly.collection.requests.filter (·.kind == .coefficient)).size
  let signCount := (assembly.collection.requests.filter (·.kind == .valueSign)).size
  logInfo m!"nested descriptor kernel checked; literals={packet.coefficients.length}, requests={assembly.collection.requests.size}, packing={packingCount}, signs={signCount}"

private unsafe def cachedControls : TermElabM Unit := withExporting (isExporting := false) do
  let supplied := #[mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedEntries,
    mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedSigns]
  let program := mkAppN (mkConst ``FiniteTowerPackets.program)
    #[mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedFacts,
      mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedSubject,
      mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerProbe.nestedGraph]
  let inventories := supplied.map (fun facts => (⟨facts⟩ : Inventory))
  let simpContext ← Simp.mkContext (simpTheorems := #[])
    (congrTheorems := ← getSimpCongrTheorems)
  let cached ← collectMany 0 program inventories simpContext
    (fun _ _ => throwError "cached nested replay invoked a producer")
  match cached.outcome with
  | .checked true proof _ =>
    kernelCheck `__finiteTowerCached
      (← mkEq (mkAppN program (cached.inventories.map Inventory.facts))
        (mkConst ``Bool.true)) proof
  | _ => throwError "cached nested descriptor did not replay"
  unless cached.requests.isEmpty do throwError "cached nested replay requested new evidence"
  let entryType ← mkAppM ``Packing #[mkConst ``FiniteTower.first]
  let absent ← mkListLit entryType []
  let some inputSigns := inventories[1]?
    | throwError "nested descriptor lost its input-sign inventory"
  let withoutPacking := #[⟨absent⟩, inputSigns]
  let omitted ← collectMany 0 program withoutPacking simpContext
    (fun _ _ => throwError "omission control invoked a producer")
  match omitted.outcome with
  | .missing application =>
    unless (← request application).kind == .coefficient do
      throwError "packing omission did not demand a coefficient record"
  | _ => throwError "nested descriptor accepted without required packing records"
  let retainedBinding ← mkAppM ``bindingEntries #[supplied[0]!]
  let readerOmission ← collectMany 0 program #[⟨retainedBinding⟩, inputSigns] simpContext
    (fun _ _ => throwError "reader omission control invoked a producer")
  match readerOmission.outcome with
  | .missing application =>
    let needed ← request application
    unless needed.kind == .coefficient do throwError "reader omission did not demand a packing"
    let belongs := mkApp (mkConst ``bindingKey) needed.polynomial
    kernelCheck `__finiteTowerReaderOmission (← mkEq belongs (mkConst ``Bool.false))
      (← mkEqRefl (mkConst ``Bool.false))
  | _ => throwError "descriptor replay accepted with only the subject-binding packings"
  let signType ← mkAppM ``ValueSign #[mkConst ``FiniteTower.first]
  let absentSigns ← mkListLit signType []
  let some packed := inventories[0]?
    | throwError "nested descriptor lost its packing inventory"
  let withoutSigns ← collectMany 0 program #[packed, ⟨absentSigns⟩] simpContext
    (fun _ _ => throwError "sign omission control invoked a producer")
  match withoutSigns.outcome with
  | .missing application =>
    unless (← request application).kind == .valueSign do
      throwError "sign omission did not demand an input-sign record"
  | _ => throwError "nested descriptor accepted without required input-sign records"
  logInfo "cached nested replay and packing/sign omission controls kernel checked"

private unsafe def rootControl : TermElabM Unit := withExporting (isExporting := false) do
  let wrong ← FiniteTowerPackets.produceRaw
    { FiniteTower.nextRaw with lower := .finite (-2), upper := .finite (-1) }
  let unbound ← FiniteTowerPackets.collect wrong ``unboundProgram
  match unbound.collection.outcome with
  | .checked true proof _ =>
    kernelCheck `__finiteTowerNegativePacket
      (← mkEq (mkAppN unbound.program (unbound.collection.inventories.map Inventory.facts))
        (mkConst ``Bool.true)) proof
  | _ => throwError "negative-root control is not a valid unbound descriptor packet"
  let rejected ← FiniteTowerPackets.collect wrong
  match rejected.collection.outcome with
  | .checked false proof _ =>
    kernelCheck `__finiteTowerWrongRoot
      (← mkEq (mkAppN rejected.program (rejected.collection.inventories.map Inventory.facts))
        (mkConst ``Bool.false)) proof
  | _ => throwError "different valid selected root was not rejected by the subject binding"
  unless !rejected.collection.requests.isEmpty do
    throwError "negative-root rejection did not check the independently constructed subject"
  for needed in rejected.collection.requests do
    unless needed.kind == .coefficient do
      throwError "negative-root rejection reached descriptor replay"
    let belongs := mkApp (mkConst ``bindingKey) needed.polynomial
    kernelCheck `__finiteTowerRejectedBinding (← mkEq belongs (mkConst ``Bool.true))
      (← mkEqRefl (mkConst ``Bool.true))
  logInfo "valid negative-root packet accepted unbound and rejected by positive-subject binding"

syntax (name := finiteTowerPackets) "#finite_tower_packets" : command
@[command_elab finiteTowerPackets]
unsafe def elaboratePackets : CommandElab := fun _ => liftTermElabM accepted

syntax (name := finiteTowerCache) "#finite_tower_cache" : command
@[command_elab finiteTowerCache]
unsafe def elaborateCache : CommandElab := fun _ => liftTermElabM cachedControls

syntax (name := finiteTowerNegative) "#finite_tower_negative" : command
@[command_elab finiteTowerNegative]
unsafe def elaborateNegative : CommandElab := fun _ => liftTermElabM rootControl

end

/-- info: nested descriptor kernel checked; literals=4, requests=15, packing=9, signs=6 -/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
#finite_tower_packets

/-- info: cached nested replay and packing/sign omission controls kernel checked -/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
#finite_tower_cache

/-- info: valid negative-root packet accepted unbound and rejected by positive-subject binding -/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
#finite_tower_negative

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
