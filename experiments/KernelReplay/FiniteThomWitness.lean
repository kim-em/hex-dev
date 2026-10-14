/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteReconstruction
public meta import HexRealClosureTheory.FiniteReconstruction
public import KernelReplay.FiniteTowerPackets
public meta import KernelReplay.FiniteTowerPackets
import all HexRealClosure.Algebraic
import all HexRealClosure.PackingReplay
import all HexSignDet.Descriptor
import all HexRealClosureTheory.PackingArithmetic
import all HexPoly.Dense
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic
import all Init.Prelude
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns
import all HexRealClosure.SignCodec
import all HexRealClosure.SignRequests
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
import all HexPoly.Euclid.DivGcd
import all KernelReplay.FiniteTowerProbe

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteThomWitness
open Hex.SignDet

/-- The complete nonconstant derivative word of the nested quadratic,
including its constant second derivative, over the whole real line. -/
@[expose] def raw : RawDescriptor (Element FiniteTower.first) Nat :=
  ⟨8, FiniteTower.nextRaw.head, .negInf, .posInf, [1, 2], [1, 1]⟩

@[expose] def requested (entries : List (Packing FiniteTower.first)) :
    RawDescriptor (Element FiniteTower.first) Nat :=
  ⟨8, (FiniteTower.requestedRaw entries).head, .negInf, .posInf, [1, 2], [1, 1]⟩

theorem requested_eq (entries : List (Packing FiniteTower.first)) : requested entries = raw := by
  unfold requested raw
  rw [FiniteTower.requestedRaw_eq entries]

/-- Decode and check a supplied graph, bind it to the independent full word,
then retain that exact raw descriptor. No graph is produced by the reader. -/
@[expose] def read? (facts : List (SignFact FiniteTower.first)) (subject packet : Codec.Json)
    (entries : List (Packing FiniteTower.first)) (signs : List (ValueSign FiniteTower.first)) :
    Option (Descriptor (Element FiniteTower.first) Nat Element.sign 8) := do
  let root ← FiniteTower.readUnbound? facts entries signs subject packet
  if equal : root.raw = requested entries then
    let bound := equal.trans (requested_eq entries)
    some (Descriptor.ofChecked Element.sign 8 raw root.evidence (by
      have checked := root.accepted
      rwa [bound] at checked))
  else none

/-- Every successful packet read retains the independently requested full raw descriptor. -/
theorem read?_raw (facts : List (SignFact FiniteTower.first)) (subject packet : Codec.Json)
    (entries : List (Packing FiniteTower.first)) (signs : List (ValueSign FiniteTower.first))
    {root : Descriptor (Element FiniteTower.first) Nat Element.sign 8}
    (accepted : read? facts subject packet entries signs = some root) : root.raw = raw := by
  unfold read? at accepted
  rcases Option.bind_eq_some_iff.mp accepted with ⟨decoded, _, accepted⟩
  dsimp only at accepted
  split at accepted
  next equal =>
    cases accepted
    rfl
  next => cases accepted

/-- Rewrite the original acceptance with its proved raw-data binding before
retaining the original request and the decoded evidence in one constructor. -/
@[expose] def restore (root : Descriptor (Element FiniteTower.first) Nat Element.sign 8)
    (bound : root.raw = raw) : Descriptor (Element FiniteTower.first) Nat Element.sign 8 :=
  Descriptor.ofChecked Element.sign 8 raw root.evidence (by
    have accepted := root.accepted
    rwa [bound] at accepted)

@[expose] def program (facts : List (SignFact FiniteTower.first)) (subject packet : Codec.Json)
    (entries : List (Packing FiniteTower.first)) (signs : List (ValueSign FiniteTower.first)) : Bool :=
  (read? facts subject packet entries signs).isSome

public meta section
open Lean Meta Elab Command

private def retainDefinition (name : Name) (value : Expr) : MetaM Unit := do
  let type ← inferType value
  let proof ← mkEqRefl value
  kernelCheck name (← inferType proof) proof
  let declaration := Declaration.defnDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteThomWitness ++ name,
    levelParams := [], type, value, hints := .abbrev, safety := .safe }
  addDecl declaration (forceExpose := true)
  compileDecl declaration

syntax (name := finiteThomWitness) "#finite_thom_witness" : command
@[command_elab finiteThomWitness]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let input ← evalExpr (RawDescriptor (Element FiniteTower.first) Nat)
    (← inferType (mkConst ``raw)) (mkConst ``raw) (checkMeta := false)
  let packet ← FiniteTowerPackets.produceRaw input
  let assembly ← FiniteTowerPackets.collect packet ``program
  let .checked true accepted _ := assembly.collection.outcome
    | throwError "complete nested derivative word was not accepted"
  let supplied := assembly.collection.inventories.map Inventory.facts
  let reader := mkAppN (mkConst ``read?) (assembly.program.getAppArgs ++ supplied)
  let (decoded, conversion) ← RationalRoot.checkedRecordProof reader
  let bound := mkAppN (mkConst ``read?_raw)
    (assembly.program.getAppArgs ++ supplied ++ #[decoded, conversion])
  let bindingType ← mkEq (← mkAppM ``Descriptor.raw #[decoded]) (mkConst ``raw)
  kernelCheck `__fullThomBinding bindingType bound
  let root ← withExporting (isExporting := false) <| withTransparency .all <|
    whnf (mkApp2 (mkConst ``restore) decoded bound)
  unless root.getAppFn.isConstOf ``Descriptor.mk do
    throwError "restored root did not expose its checked constructor"
  retainDefinition `root root
  let entries := supplied[0]!
  let signs := supplied[1]!
  retainDefinition `entries entries
  retainDefinition `signs signs
  let equality ← mkEq (mkAppN assembly.program supplied) (mkConst ``Bool.true)
  kernelCheck `__fullThomAcceptance equality accepted
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteThomWitness.accepted,
    levelParams := [], type := equality, value := accepted })
  let impossible := { input with signs := [1, -1] }
  let wrongPacket : FiniteTowerPackets.Packet :=
    ⟨SignRequests.binding (Element.codec ValueCodec.rat) ValueCodec.nat impossible,
      packet.graph, packet.coefficients⟩
  let rejected ← FiniteTowerPackets.collect wrongPacket ``FiniteTowerPackets.unboundProgram
  let .checked false proof _ := rejected.collection.outcome
    | throwError "negative constant second derivative was accepted"
  kernelCheck `__fullThomRejection
    (← mkEq (mkAppN rejected.program (rejected.collection.inventories.map Inventory.facts))
      (mkConst ``Bool.false)) proof
  logInfo "complete nested derivative word reconstructed from literal packets; impossible second-derivative sign rejected"

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
/-- info: complete nested derivative word reconstructed from literal packets; impossible second-derivative sign rejected -/
#guard_msgs in
#finite_thom_witness

end Hex.RealClosure.Algebraic.KernelReplay.FiniteThomWitness

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteThomWitness.root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteThomWitness.root
