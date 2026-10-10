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
def elaborate : CommandElab := fun _ => liftTermElabM do
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
  logInfo "literal nested descriptor accepted with retained inventories and ordinary kernel"

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
/-- info: literal nested descriptor accepted with retained inventories and ordinary kernel -/
#guard_msgs in
#finite_witness_probe

/-- The descriptor retains the actual decoded packet's literal leaf node. -/
@[expose] def root : Descriptor (Element FiniteTower.first) Nat Element.sign 8 :=
  Descriptor.ofChecked Element.sign 8 FiniteTower.nextRaw (.leaf FiniteDataProbe.decodedNode)
    ((packed_eq FiniteTowerProbe.nestedEntries FiniteTowerProbe.nestedSigns).symm.trans accepted)

theorem root_data : Packing.DescriptorData FiniteTowerProbe.nestedEntries
    FiniteTowerProbe.nestedSigns FiniteDataProbe.read root.raw root.evidence :=
  FiniteDataProbe.descriptorData

end Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness.root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness.root

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness.root_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteWitness.root_data
