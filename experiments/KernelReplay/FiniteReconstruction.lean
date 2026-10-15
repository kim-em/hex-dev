/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteReconstruction
public meta import HexRealClosureTheory.FiniteReconstruction
import all HexRealClosureTheory.FiniteReconstruction
public import KernelReplay.FiniteBase
public import KernelReplay.FiniteJoint
public meta import KernelReplay.FiniteData
import all HexRealClosure.BaseContext
import all HexRealClosureTheory.BaseFinite
import all HexPoly.Dense
import all HexRationalFn.Basic
import all Init.Data.Array.Basic
import all Init.Data.Rat.Basic

import all HexRealClosure.Algebraic
import all HexRealClosure.PackingReplay
import all HexSignDet.Descriptor
import all KernelReplay.FiniteData
import all KernelReplay.FiniteJoint
import all HexRealClosureTheory.PackingArithmetic
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
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteReconstructionProbe

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat
local instance : Field (RationalFn (RationalFn Rat)) := HexPolyTheory.fieldOfGrind

/-- Use the actual two-infinitesimal history, with its rational provider
realization. No real coefficient reader or sign agreement is an input. -/
noncomputable def following : FiniteBaseProbe.base.chain.Realization FiniteBaseProbe.registry :=
  .infinitesimal FiniteBaseProbe.first.chain (.infinitesimal FiniteBaseProbe.rational.chain
    (.real .base (.rational FiniteBaseProbe.registry) .base))

private theorem rationalZero : FiniteDataProbe.read 0 = 0 := by simp [FiniteDataProbe.read]
private theorem rationalUnit : FiniteDataProbe.read 1 = 1 := by simp [FiniteDataProbe.read]

private theorem successorData : Packing.Inventory.Data FiniteJoint.next [] [] []
    (FiniteJoint.readAt FiniteJoint.alpha) := by
  refine ⟨FiniteJoint.nextData, ?_, ?_, ?_⟩
  all_goals intros; simp_all

public meta section
open Lean Meta Elab Command

private def retain (name : Name) (result : FiniteData.Reconstruction) : MetaM Unit := do
  kernelCheck name result.type result.proof
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteReconstructionProbe ++ name,
    levelParams := [], type := result.type, value := result.proof })

private def reject (message : String) (action : MetaM α) : MetaM Unit := do
  try
    let _ ← action
    throwError "reconstruction accepted a negative control"
  catch error =>
    unless (← error.toMessageData.toString).startsWith message do throw error

private def supportShape (blocks : Array Expr) (combined : Expr) : MetaM Unit := do
  if blocks.isEmpty then return
  let mut pending := [(combined, 0)]
  let mut obtained : Array Expr := #[]
  let mut depth := 0
  while !pending.isEmpty do
    let (value, current) :: rest := pending | throwError "support traversal lost its next block"
    pending := rest
    if value.getAppFn.isConstOf ``List.append then
      let args := value.getAppArgs
      pending := (args[args.size - 2]!, current + 1) ::
        (args.back!, current + 1) :: pending
    else
      obtained := obtained.push value
      depth := max depth current
  unless obtained == blocks do throwError "support reassociation changed its ordered blocks"
  let mut width := 1
  let mut bound := 0
  while width < blocks.size do
    width := 2 * width
    bound := bound + 1
  unless depth ≤ bound do throwError "support reassociation retained a linear append chain"

private def supportLists : MetaM Unit := do
  let nat := mkConst ``Nat
  for count in #[0, 1, 2, 3, 5, 17] do
    let mut blocks := #[]
    let mut values := []
    for i in [:count] do
      let current := [toExpr (i % 3), toExpr (i + 1)]
      blocks := blocks.push (← mkListLit nat current)
      values := values ++ current
    let combined ← FiniteData.appendSupport nat blocks
    supportShape blocks combined
    let expected ← mkListLit nat values
    kernelCheck `__finiteSupportOrder (← mkEq combined expected) (← mkEqRefl expected)
  -- The shape check also covers many opaque blocks without evaluating them.
  withLocalDeclD `block (← mkAppM ``List #[nat]) fun block => do
    let blocks := Array.replicate 2049 block
    let combined ← FiniteData.appendSupport nat blocks
    supportShape blocks combined

syntax (name := finiteReconstructionProbe) "#finite_reconstruction_probe" : command
@[command_elab finiteReconstructionProbe]
def elaborate : CommandElab := fun _ => liftTermElabM do
  supportLists
  let base := mkConst ``FiniteBaseProbe.base
  let coefficient ← mkAppM ``BaseContext.Element #[base]
  let readType ← mkArrow coefficient (mkConst ``Real)
  let extra ← mkListLit coefficient [mkConst ``FiniteBaseProbe.epsilon]
  let noProducer : FiniteData.Supplier := fun _ =>
    throwError "reconstruction attempted to produce a record after choosing a point"
  withLocalDeclD `read readType fun read => do
    let operation ← mkAppM ``Transport.Sum
      #[read, mkConst ``FiniteBaseProbe.left, mkConst ``FiniteBaseProbe.right]
    let leaf : FiniteData.Leaf := ⟨operation, ← getLCtx, ← getLocalInstances⟩
    let leading ← mkAppM ``Transport.Leading #[read, mkConst ``FiniteBaseProbe.left]
    let frontier ← FiniteData.frontier leading FiniteData.dependencyBoundary
    let some leadingLeaf := frontier[0]? | throwError "leading dependency disappeared"
    unless frontier.size == 1 && leadingLeaf.type.getAppFn.isConstOf ``Transport.Leading do
      throwError "leading dependency lost its original polynomial"
    let discovery : FiniteData.Discovery := ⟨#[], #[], #[leaf, leadingLeaf], true, #[]⟩
    let result ← FiniteData.reconstruct base (mkConst ``following) read discovery extra noProducer
    unless result.prefixes.isEmpty do throwError "base reconstruction invented an algebraic level"
    if result.type.hasFVar || result.proof.hasFVar then
      throwError "base reconstruction retained a temporary reader"
    let expected ← mkAppM ``List.append #[extra,
      ← mkAppM ``List.append #[← mkAppM ``Transport.Inventory.coefficients #[mkConst ``FiniteBaseProbe.left],
        ← mkAppM ``Transport.Inventory.coefficients #[mkConst ``FiniteBaseProbe.right]]]
    let expected ← mkAppM ``List.append #[expected,
      ← mkAppM ``Transport.Inventory.coefficients #[mkConst ``FiniteBaseProbe.left]]
    unless ← withTransparency .all (isDefEq result.support expected) do
      throwError "base reconstruction lost original coefficients through cancellation"
    retain `baseJoint result
    reject "unsaturated finite dependencies" <|
      FiniteData.reconstruct base (mkConst ``following) read { discovery with saturated := false }
        extra noProducer
    let unresolved : FiniteData.Leaf := ⟨mkConst ``False, ← getLCtx, ← getLocalInstances⟩
    reject "missing finite replay evidence" <|
      FiniteData.reconstruct base (mkConst ``following) read
        { discovery with leaves := #[unresolved] } extra noProducer
    let contextType ← Elab.Term.elabType (← `(Context
      (BaseContext.Element FiniteBaseProbe.base) Nat BaseContext.Element.sign 37))
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let contextType ← instantiateMVars contextType
    withLocalDeclD `context contextType fun context => do
      let entryType ← mkAppM ``List #[← mkAppM ``Packing #[context]]
      let recordType ← mkAppM ``List #[← mkAppM ``ValueSign #[context]]
      let factType ← mkAppM ``List #[← mkAppM ``InverseFact #[context]]
      withLocalDeclD `entries entryType fun entries =>
        withLocalDeclD `records recordType fun records =>
          withLocalDeclD `facts factType fun facts => do
            let readerType ← mkArrow (← mkAppM ``Element #[context]) (mkConst ``Real)
            withLocalDeclD `reader readerType fun reader => do
              let level : FiniteData.Level := ⟨context, entries, records, facts, read, reader⟩
              let result ← FiniteData.reconstruct base (mkConst ``following) read
                ⟨#[level], #[], #[], true, #[]⟩ extra noProducer
              unless result.prefixes.size == 1 do throwError "reconstruction lost its selected coordinate"
              if result.type.hasFVar || result.proof.hasFVar then
                throwError "joint existential retained discovery locals"
              retain `selectedJoint result
              withLocalDeclD `other readType fun other => do
                reject "first finite level does not follow the base reader" <|
                  FiniteData.reconstruct base (mkConst ``following) other
                    ⟨#[level], #[], #[], true, #[]⟩ extra noProducer
  let first ← FiniteData.Prefix.ofData (mkConst ``FiniteJoint.firstData)
    (mkConst ``rationalZero) (mkConst ``rationalUnit)
  let leading ← mkAppM ``Transport.Leading #[first.reader,
    ← mkAppM ``Hex.SignDet.RawDescriptor.head #[mkConst ``FiniteTower.nextRaw]]
  let _ ← FiniteData.buildClosed leading (first.supplyAll FiniteDataProbe.supply)
  let next := mkConst ``FiniteJoint.next
  let decisions : FiniteData.Supplier := fun requested => do
    if requested.getAppFn.isConstOf ``Packing.Inventory.Data then
      let proof := mkConst ``successorData
      if ← withTransparency .all (isDefEq (← inferType proof) requested) then
        return some proof
    FiniteDataProbe.supply requested
  let second ← first.extend decisions next
    (← mkListLit (← mkAppM ``Packing #[next]) [])
    (← mkListLit (← mkAppM ``ValueSign #[next]) [])
    (← mkListLit (← mkAppM ``InverseFact #[next]) [])
  let (type, proof) ← FiniteData.Prefix.joint #[first, second]
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteReconstructionProbe.nestedJoint,
    levelParams := [], type, value := proof })
  reject "joint prefixes are not in predecessor order" <| FiniteData.Prefix.joint #[second, first]
  logInfo "staged reconstruction retained cancellation inputs, all three inventories and nested shared witnesses; unsaturated, unresolved and wrong-reader inputs rejected"

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
/-- info: staged reconstruction retained cancellation inputs, all three inventories and nested shared witnesses; unsaturated, unresolved and wrong-reader inputs rejected -/
#guard_msgs in
#finite_reconstruction_probe

end Hex.RealClosure.Algebraic.KernelReplay.FiniteReconstructionProbe

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteReconstructionProbe.baseJoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteReconstructionProbe.baseJoint

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteReconstructionProbe.selectedJoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteReconstructionProbe.selectedJoint

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteReconstructionProbe.nestedJoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteReconstructionProbe.nestedJoint
