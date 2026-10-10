/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.FiniteScalars
public meta import HexRealClosureMathlib.FiniteScalars
public import KernelReplay.FiniteJoint
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
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteLiftProbe

private theorem zero : FiniteDataProbe.read 0 = 0 := by simp [FiniteDataProbe.read]
private theorem unit : FiniteDataProbe.read 1 = 1 := by simp [FiniteDataProbe.read]

public meta section
open Lean Meta Elab Command

syntax (name := finiteLiftProbe) "#finite_lift_probe" : command
@[command_elab finiteLiftProbe]
def elaborate : CommandElab := fun _ => liftTermElabM do
  let level ← FiniteData.Prefix.ofData (mkConst ``FiniteJoint.firstData)
    (mkConst ``zero) (mkConst ``unit)
  let supplier := level.supplyAll FiniteDataProbe.supply
  let .forallE _ source _ _ ← whnf (← inferType level.reader) |
    throwError "invalid scalar reader"
  let scalarType (n : Nat) : MetaM Expr := do
    let native ← mkAppOptM ``Nat.cast #[some source, none, some (toExpr n)]
    let real ← mkAppOptM ``Nat.cast #[some (mkConst ``Real), none, some (toExpr n)]
    mkEq (mkApp level.reader native) real
  for (n, name) in #[(0, `zeroLaw), (1, `unitLaw), (2, `castLaw)] do
    let type ← scalarType n
    let proof ← FiniteData.buildClosed type supplier
    addDecl (.thmDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteLiftProbe ++ name,
      levelParams := [], type, value := proof })
  let nativeZero ← mkAppOptM ``Zero.zero #[some source, none]
  let realZero ← mkAppOptM ``Zero.zero #[some (mkConst ``Real), none]
  let zeroType ← mkEq (mkApp level.reader nativeZero) realZero
  let noLookup : FiniteData.Supplier := fun type =>
    throwError "zero law delegated an obligation: {type}"
  let _ ← FiniteData.buildClosed zeroType (level.supplyAll noLookup)
  try
    let _ ← FiniteData.buildClosed (← scalarType 3) supplier
    throwError "finite scalar law accepted an absent constant key"
  catch error =>
    unless (← error.toMessageData.toString).startsWith "missing finite replay evidence" do
      throw error
  let product ← mkAppM ``Transport.Product #[level.reader,
    mkConst ``FiniteDataProbe.unit, mkConst ``FiniteDataProbe.two]
  let proof ← FiniteData.buildClosed product supplier
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteLiftProbe.product
    levelParams := [], type := product, value := proof })
  let root := mkConst ``FiniteWitness.root
  let raw ← mkAppM ``Hex.SignDet.Descriptor.raw #[root]
  let evidence ← mkAppM ``Hex.SignDet.Descriptor.evidence #[root]
  let sourceSign ← Elab.Term.elabTerm (← `(Element.sign (context := FiniteTower.first))) none
  let targetSign ← Elab.Term.elabTerm (← `(fun x : ℝ => (SignType.sign x : Int))) none
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let type ← mkAppM ``Transport.Finite.DescriptorData #[level.reader,
    ← instantiateMVars sourceSign, ← instantiateMVars targetSign, raw, evidence]
  let proof ← FiniteData.buildClosed type supplier
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteLiftProbe.descriptor
    levelParams := [], type, value := proof })
  let next := mkConst ``FiniteJoint.next
  let nextEntries ← mkListLit (← mkAppM ``Packing #[next]) []
  let nextRecords ← mkListLit (← mkAppM ``ValueSign #[next]) []
  let nextFacts ← mkListLit (← mkAppM ``InverseFact #[next]) []
  let second ← level.extend FiniteDataProbe.supply next nextEntries nextRecords nextFacts
  let dataType ← inferType second.data
  kernelCheck `__finiteSuccessorData dataType second.data
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteLiftProbe.nextData,
    levelParams := [], type := dataType, value := second.data })
  let selected ← mkAppM ``Context.finitePoint_spec
    #[second.read, second.zero, second.unit, second.descriptor]
  let selectedType ← inferType selected
  kernelCheck `__finiteSuccessorPoint selectedType selected
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteLiftProbe.selected,
    levelParams := [], type := selectedType, value := selected })
  logInfo "finite predecessor supplier generated scalar, arithmetic, descriptor and successor proofs; missing cast key rejected"

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
/-- info: finite predecessor supplier generated scalar, arithmetic, descriptor and successor proofs; missing cast key rejected -/
#guard_msgs in
#finite_lift_probe

end Hex.RealClosure.Algebraic.KernelReplay.FiniteLiftProbe

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteLiftProbe.descriptor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteLiftProbe.descriptor

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteLiftProbe.nextData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteLiftProbe.nextData
