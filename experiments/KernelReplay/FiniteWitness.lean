/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteData
public meta import KernelReplay.FiniteData
import all HexRealClosure.Algebraic
import all HexRealClosure.PackingReplay
import all HexSignDet.Descriptor
import all KernelReplay.FiniteData
import all HexRealClosureMathlib.PackingArithmetic
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
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness
open Hex.SignDet

/-- Check the literal decoded node using only retained arithmetic and sign
records. No producer supplies a proof or a missing record in this check. -/
@[expose] def packed (entries : List (Packing FiniteTower.first))
    (signs : List (ValueSign FiniteTower.first)) : Bool :=
  @RawDescriptor.check (Element FiniteTower.first) Nat _ _
    (Element.replayOne (inferInstance : One Rat) rfl entries)
    (Element.replayAdd (inferInstance : Add Rat) rfl entries)
    (Element.replaySub (inferInstance : Sub Rat) rfl entries)
    (Element.replayMul (inferInstance : Add Rat) (inferInstance : Mul Rat) rfl rfl entries)
    (Element.replayNatCast (inferInstance : NatCast Rat) rfl entries) _
    (Element.replaySign signs) 8 (FiniteTower.requestedRaw entries) (.leaf FiniteDataProbe.decodedNode)

theorem packed_eq (entries : List (Packing FiniteTower.first))
    (signs : List (ValueSign FiniteTower.first)) :
    packed entries signs = FiniteTower.nextRaw.check Element.sign 8
      (.leaf FiniteDataProbe.decodedNode) := by
  unfold packed
  rw [FiniteTower.requestedRaw_eq entries]
  rw [Element.replayOne_eq (inferInstance : One Rat) rfl entries,
    Element.replayAdd_eq (inferInstance : Add Rat) rfl entries,
    Element.replaySub_eq (inferInstance : Sub Rat) rfl entries,
    Element.replayMul_eq (inferInstance : Add Rat) (inferInstance : Mul Rat) rfl rfl entries,
    Element.replayNatCast_eq (inferInstance : NatCast Rat) rfl entries]
  have same : Element.replaySign signs = Element.sign := funext (Element.replaySign_eq signs)
  rw [same]

public meta section
open Lean Meta Elab Command

syntax (name := finiteWitnessProbe) "#finite_witness_probe" : command
@[command_elab finiteWitnessProbe]
def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) <| withTransparency .all do
  let expression := mkAppN (mkConst ``packed)
    #[mkConst ``FiniteTowerProbe.nestedEntries, mkConst ``FiniteTowerProbe.nestedSigns]
  let context ← Simp.mkContext (simpTheorems := #[])
    (congrTheorems := ← getSimpCongrTheorems)
  let (outcome, _) ← assemble expression context
  let .checked true proof _ := outcome
    | throwError "literal nested descriptor did not check with retained inventories"
  let type ← mkEq expression (mkConst ``Bool.true)
  kernelCheck `__finiteWitnessAcceptance type proof
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness.accepted
    levelParams := [], type, value := proof })
  let reader := mkAppN (mkConst ``FiniteTower.readNext?)
    #[mkConst ``FiniteTowerProbe.nestedFacts, mkConst ``FiniteTowerProbe.nestedEntries,
      mkConst ``FiniteTowerProbe.nestedSigns, mkConst ``FiniteTowerProbe.nestedSubject,
      mkConst ``FiniteTowerProbe.nestedGraph]
  let (decoded, conversion) ← RationalRoot.checkedRecordProof reader
  let conversionType ← mkEq reader (← mkAppM ``Option.some #[decoded])
  let _ ← auditProof conversion conversionType
  kernelCheck `__finiteOriginalReader conversionType conversion
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness.root_read,
    levelParams := [], type := conversionType, value := conversion })
  let conversion := mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness.root_read
  let original := mkConst ``FiniteTowerProbe.nestedRoot
  let present ← mkAppM ``Option.some_get #[mkConst ``FiniteTowerProbe.nestedAccepted]
  let decodedSome ← mkAppM ``Eq.trans #[present, conversion]
  let same ← mkAppM ``Option.some.inj #[decodedSome]
  let originalEvidence ← mkAppM ``Descriptor.evidence #[original]
  let decodedEvidence ← mkAppM ``Descriptor.evidence #[decoded]
  let requestedEvidence ← mkAppM ``Replay.leaf #[mkConst ``FiniteDataProbe.decodedNode]
  unless ← withTransparency .all (isDefEq decodedEvidence requestedEvidence) do
    throwError "original nested replay differs from the retained decoded node"
  let evidenceType ← mkEq originalEvidence requestedEvidence
  let carrier ← inferType original
  withLocalDeclD `root carrier fun root => do
    let getter ← mkLambdaFVars #[root] (← mkAppM ``Descriptor.evidence #[root])
    let evidenceProof ← mkAppM ``congrArg #[getter, same]
    kernelCheck `__finiteOriginalEvidence evidenceType evidenceProof
    addDecl (.thmDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness.root_evidence,
      levelParams := [], type := evidenceType, value := evidenceProof })
  logInfo "literal nested descriptor accepted with retained inventories and ordinary kernel"

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
/-- info: literal nested descriptor accepted with retained inventories and ordinary kernel -/
#guard_msgs in
#finite_witness_probe

/-- Retain the original nested descriptor, including its replay evidence. -/
@[expose] def root : Descriptor (Element FiniteTower.first) Nat Element.sign 8 :=
  FiniteTowerProbe.nestedRoot

theorem root_data : Packing.DescriptorData FiniteTowerProbe.nestedEntries
    FiniteTowerProbe.nestedSigns FiniteDataProbe.read root.raw root.evidence := by
  rw [root, FiniteTowerProbe.nestedRoot_raw, root_evidence]
  exact FiniteDataProbe.descriptorData

end Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness.root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness.root

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness.root_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness.root_data
