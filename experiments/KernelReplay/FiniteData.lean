/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.FiniteData
public meta import HexRealClosureMathlib.FiniteData
public import KernelReplay.FiniteTowerProbe
public meta import KernelReplay.FiniteTowerProbe
import all HexRealClosure.Algebraic
import all HexRealClosureMathlib.PackingArithmetic
import all HexPoly.Dense
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic
import all Init.Prelude
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns
import all HexRealClosure.PackingReplay
import all HexRealClosure.SignCodec
import all HexRealClosure.SignRequests
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
import all HexPoly.Euclid.DivGcd
import all KernelReplay.FiniteTowerProbe

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteDataProbe
open Hex.SignDet

@[expose] def read (q : Rat) : ℝ := q

private theorem closed : Transport.Closed read (fun _ => True) := by
  refine ⟨trivial, ?_, ?_, ?_, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros; simp [read]

theorem sums (p q : DensePoly Rat) : Transport.Sum read p q :=
  Transport.Sum.of_closed read (fun _ => True) closed p q
    (fun _ _ => trivial) (fun _ _ => trivial)

theorem products (p q : DensePoly Rat) : Transport.Product read p q :=
  Transport.Product.of_closed read (fun _ => True) closed p q
    (fun _ _ => trivial) (fun _ _ => trivial)

theorem differences (p q : DensePoly Rat) : Transport.Difference read p q :=
  Transport.Difference.of_closed read (fun _ => True) closed p q
    (fun _ _ => trivial) (fun _ _ => trivial)

theorem casts (n : Nat) : read (n : Rat) = (n : ℝ) := by simp [read]

@[expose] def unit : DensePoly (Element FiniteTower.first) := DensePoly.C 1
@[expose] def two : DensePoly (Element FiniteTower.first) := DensePoly.C 2

public meta section
open Lean Meta Elab Command

private def closeProof (type proof : Expr) : MetaM (Expr × Expr) := do
  let binders := (← getLCtx).getFVarIds.map mkFVar
  return (← mkForallFVars binders type, ← mkLambdaFVars binders proof)

private def supply (type : Expr) : MetaM (Option Expr) := do
  let arguments := type.getAppArgs
  if type.getAppFn.isConstOf ``Transport.Sum then
    return some (← mkAppM ``sums #[arguments[arguments.size - 2]!, arguments.back!])
  if type.getAppFn.isConstOf ``Transport.Product then
    return some (← mkAppM ``products #[arguments[arguments.size - 2]!, arguments.back!])
  if type.getAppFn.isConstOf ``Transport.Difference then
    return some (← mkAppM ``differences #[arguments[arguments.size - 2]!, arguments.back!])
  if type.getAppFn.isConstOf ``Eq && arguments.size == 3 then
    let left := arguments[1]!
    if left.getAppFn.isConstOf ``read then
      let cast := left.getAppArgs.back!
      if cast.isApp then
        let n := cast.getAppArgs.back!
        if (← inferType n).isConstOf ``Nat then
          let proof ← mkAppM ``casts #[n]
          if ← isDefEq (← inferType proof) type then return some proof
  unless type.getAppFn.isConstOf ``Eq && arguments[0]!.isConstOf ``Bool do return none
  let decision ← mkDecide type
  let statement ← mkEq decision (mkConst ``Bool.true)
  let reflexive ← mkEqRefl (mkConst ``Bool.true)
  let (statement, reflexive) ← closeProof statement reflexive
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let declaration := Declaration.thmDecl {
    name := `__finiteDataDecision
    levelParams := []
    type := statement
    value := reflexive }
  unless ← acceptKernel ((← getEnv).toKernelEnv.addDecl options declaration) do return none
  let proof ← mkDecideProof type
  let (closedType, closedProof) ← closeProof type proof
  kernelCheck `__finiteDataLookup closedType closedProof
  return some proof

private def productType (entries : Expr) : MetaM Expr :=
  mkAppM ``Packing.ProductData
    #[entries, mkConst ``read, mkConst ``unit, mkConst ``two]

syntax (name := finiteDataProbe) "#finite_data_probe" : command
@[command_elab finiteDataProbe]
def elaborateProbe : CommandElab := fun _ => liftTermElabM do
  let entries := mkConst ``FiniteTowerProbe.nestedEntries
  let type ← productType entries
  let proof ← FiniteData.buildClosed type supply
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteDataProbe.productData
    levelParams := [], type, value := proof })
  let indexType ← Elab.Term.elabType (← `(∀ i : Fin 3,
    (Packing.find FiniteTowerProbe.nestedEntries (DensePoly.C (1 : Rat))).isSome = true))
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let indexType ← instantiateMVars indexType
  let _ ← FiniteData.buildClosed indexType supply
  let entryType ← mkAppM ``Packing #[mkConst ``FiniteTower.first]
  let missingType ← productType (← mkListLit entryType [])
  let leaves ← FiniteData.leaves missingType supply
  unless leaves.size > 0 do throwError "finite support discovery missed required packing keys"
  try
    let _ ← FiniteData.buildClosed missingType supply
    throwError "finite-data assembly accepted a missing packing key"
  catch error =>
    let message ← error.toMessageData.toString
    unless message.startsWith "missing finite replay evidence for" do throw error
  logInfo "finite product data built from retained original keys; missing inventory rejected"

syntax (name := finiteDescriptorProbe) "#finite_descriptor_probe" : command
@[command_elab finiteDescriptorProbe]
def elaborateDescriptor : CommandElab := fun _ => liftTermElabM do
  let raw := mkConst ``FiniteTower.nextRaw
  let head ← mkAppM ``Hex.SignDet.RawDescriptor.head #[raw]
  let degree ← mkAppM ``DensePoly.natDegree #[head]
  let type ← mkAppM ``Packing.DerivativeData #[mkConst ``FiniteTowerProbe.nestedEntries,
    mkConst ``read, head, degree]
  let leaves ← FiniteData.leaves type supply
  unless leaves.isEmpty do throwError "nested derivative data needs additional evidence"
  let proof ← FiniteData.buildClosed type supply
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteDataProbe.derivativeData
    levelParams := [], type, value := proof })
  logInfo "nested derivative data checked from retained original packing keys"

syntax (name := finiteNodeProbe) "#finite_node_probe" : command
@[command_elab finiteNodeProbe]
def elaborateNode : CommandElab := fun _ => liftTermElabM do
  let graphReader ← Elab.Term.elabTerm (← `(
    (Hex.SignDet.Codec.readGraph
      (Element.signCodec Hex.SignDet.ValueCodec.rat FiniteTowerProbe.nestedFacts)
      Hex.SignDet.ValueCodec.nat 8 FiniteTower.nextRaw.head
      FiniteTower.nextRaw.lower FiniteTower.nextRaw.upper
      FiniteTowerProbe.nestedGraph).toOption)) none
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let graphReader ← instantiateMVars graphReader
  let graph ← RationalRoot.checkedRecord graphReader
  let entryReader ← mkAppM ``GetElem?.getElem? #[← mkAppM ``Hex.SignDet.Dag.entries #[graph],
    ← mkAppM ``Hex.SignDet.Dag.root #[graph]]
  let entry ← RationalRoot.checkedRecord entryReader
  let node ← mkAppM ``Hex.SignDet.Dag.Entry.node #[entry]
  let declaration := Declaration.defnDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteDataProbe.decodedNode
    levelParams := [], type := ← inferType node, value := node
    hints := .abbrev, safety := .safe }
  addDecl declaration (forceExpose := true)
  compileDecl declaration
  let node := mkConst `Hex.RealClosure.Algebraic.KernelReplay.FiniteDataProbe.decodedNode
  let raw := mkConst ``FiniteTower.nextRaw
  let type ← mkAppM ``Packing.NodeData #[mkConst ``FiniteTowerProbe.nestedEntries,
    mkConst ``FiniteTowerProbe.nestedSigns, mkConst ``read,
    ← mkAppM ``Hex.SignDet.RawDescriptor.head #[raw],
    ← mkAppM ``Hex.SignDet.RawDescriptor.lower #[raw],
    ← mkAppM ``Hex.SignDet.RawDescriptor.upper #[raw],
    ← mkAppM ``Hex.SignDet.RawDescriptor.queries #[raw], node]
  let proof ← FiniteData.buildClosed type supply
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteDataProbe.nodeData
    levelParams := [], type, value := proof })
  logInfo "decoded nested node data checked from retained original packing and sign keys"

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
/-- info: finite product data built from retained original keys; missing inventory rejected -/
#guard_msgs in
#finite_data_probe

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
/-- info: nested derivative data checked from retained original packing keys -/
#guard_msgs in
#finite_descriptor_probe

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
/-- info: decoded nested node data checked from retained original packing and sign keys -/
#guard_msgs in
#finite_node_probe

theorem descriptorData : Packing.DescriptorData FiniteTowerProbe.nestedEntries
    FiniteTowerProbe.nestedSigns read FiniteTower.nextRaw (.leaf decodedNode) :=
  ⟨derivativeData, nodeData.head, nodeData⟩

end Hex.RealClosure.Algebraic.KernelReplay.FiniteDataProbe

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteDataProbe.productData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteDataProbe.productData

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteDataProbe.descriptorData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteDataProbe.descriptorData
