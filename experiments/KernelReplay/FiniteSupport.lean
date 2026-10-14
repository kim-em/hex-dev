/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteData
public meta import KernelReplay.FiniteData
public import HexRealClosureTheory.FiniteSupport
public meta import HexRealClosureTheory.FiniteSupport
import all HexRealClosure.Algebraic
import all HexRealClosureTheory.PackingArithmetic
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
import all KernelReplay.FiniteData

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteSupportProbe
open Lean Meta Elab Command

private def productType (inventories : Array Inventory) : MetaM Expr := do
  let some entries := inventories[0]? | throwError "product support lost its inventory"
  mkAppM ``Packing.ProductData #[entries.facts, mkConst ``FiniteDataProbe.read,
    mkConst ``FiniteDataProbe.unit, mkConst ``FiniteDataProbe.two]

private unsafe def packing (lookup : FiniteData.Lookup) (_ : Array Inventory) :
    MetaM (Option Expr) := do
  unless lookup.request.kind == .coefficient do throwError "unexpected product support kind"
  return some (← FiniteTowerPackets.packing lookup.key)

syntax (name := finiteSupportProbe) "#finite_support_probe" : command
@[command_elab finiteSupportProbe]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let owner := mkConst ``FiniteTower.first
  let entryType ← mkAppM ``Packing #[owner]
  let entries ← mkListLit entryType []
  let initial : Array Inventory := #[⟨entries⟩]
  let blocked ← FiniteData.collectSupport 0 initial productType FiniteDataProbe.supply
    (fun _ _ => throwError "zero-fuel discovery invoked a producer")
  let .unresolved obligations := blocked.result | throwError "empty support was accepted"
  unless !obligations.isEmpty do throwError "empty support lost its obligations"
  for obligation in obligations do
    if let some lookup ← obligation.lookup? then
      unless lookup.request.kind == .coefficient do throwError "product discovery changed kind"
      lookup.leaf.withContext do
        unless ← isDefEq lookup.request.context owner do throwError "product discovery changed owner"
        unless ← isDefEq lookup.inventory entries do throwError "product discovery changed inventory"
  let collected ← FiniteData.collectSupport 10 initial productType FiniteDataProbe.supply packing
  let .complete type proof := collected.result | throwError "finite product support was not collected"
  unless !collected.requests.isEmpty do throwError "finite product collection produced no records"
  kernelCheck `__finiteSupportProduct type proof
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteSupportProbe.productData
    levelParams := [], type, value := proof })
  let cached ← FiniteData.collectSupport 0 collected.inventories productType FiniteDataProbe.supply
    (fun _ _ => throwError "cached finite support invoked a producer")
  let .complete _ _ := cached.result | throwError "cached finite support did not replay"
  unless cached.requests.isEmpty do throwError "cached finite support requested another record"
  let wrong ← FiniteTowerPackets.packing (← Elab.Term.elabTerm (← `(DensePoly.C (0 : Rat))) none)
  try
    let _ ← FiniteData.collectSupport 1 initial productType FiniteDataProbe.supply
      (fun _ _ => pure (some wrong))
    throwError "finite support accepted a different original key"
  catch error =>
    unless (← error.toMessageData.toString).startsWith "finite support record binds a different key" do
      throw error
  let signType ← mkAppM ``ValueSign #[owner]
  let signs ← mkListLit signType []
  let signStatement (inventories : Array Inventory) : MetaM Expr := do
    let some records := inventories[0]? | throwError "sign support lost its inventory"
    let found ← mkAppM ``ValueSign.find #[records.facts, mkConst ``FiniteTower.generator]
    mkEq (← mkAppM ``Option.isSome #[found]) (mkConst ``Bool.true)
  let signed ← FiniteData.collectSupport 1 #[⟨signs⟩] signStatement FiniteDataProbe.supply
    (fun lookup _ => do
      unless lookup.request.kind == .valueSign do throwError "sign discovery changed kind"
      let some value := lookup.request.value | throwError "sign discovery lost its operand"
      return some (← FiniteTowerPackets.sign value))
  let .complete signType signProof := signed.result | throwError "input sign support was not collected"
  kernelCheck `__finiteSupportSign signType signProof
  let inverseType ← mkAppM ``InverseFact #[owner]
  let inverseFacts ← mkListLit inverseType []
  let found ← mkAppM ``InverseFact.find #[inverseFacts, mkConst ``FiniteTower.generator]
  let inverseStatement ← mkEq (← mkAppM ``Option.isSome #[found]) (mkConst ``Bool.true)
  let inverses ← FiniteData.collectSupport 0 #[⟨inverseFacts⟩] (fun _ => pure inverseStatement)
    FiniteDataProbe.supply (fun _ _ => throwError "inverse discovery invoked a producer")
  let .unresolved missing := inverses.result | throwError "absent inverse support was accepted"
  let some leaf := missing[0]? | throwError "inverse discovery lost its obligation"
  let some lookup ← leaf.lookup? | throwError "inverse lookup was not recognized"
  unless lookup.request.kind == .inverse do throwError "inverse discovery changed kind"
  leaf.withContext do
    unless ← isDefEq lookup.key (mkConst ``FiniteTower.generator) do
      throwError "inverse discovery changed the stored operand"
    let polynomial ← mkAppM ``Element.polynomial #[mkConst ``FiniteTower.generator]
    unless ← isDefEq lookup.request.polynomial polynomial do
      throwError "inverse discovery computed a candidate instead of retaining the operand"
  let readerType ← mkArrow (mkConst ``Rat) (mkConst ``Real)
  let unfinished ← withLocalDeclD `read readerType fun read => do
    let statement (inventories : Array Inventory) : MetaM Expr := do
      let some entries := inventories[0]? | throwError "open support lost its inventory"
      mkAppM ``Packing.ProductData #[entries.facts, read,
        mkConst ``FiniteDataProbe.unit, mkConst ``FiniteDataProbe.two]
    let decisions : FiniteData.Supplier := fun type => do
      let args := type.getAppArgs
      if type.getAppFn.isConstOf ``Eq && args.size == 3 && args[0]!.isConstOf ``Bool then
        FiniteDataProbe.supply type
      else pure none
    FiniteData.collectSupport 10 initial statement decisions packing
  let .unresolved arithmetic := unfinished.result
    | throwError "open reader's arithmetic was assumed"
  unless !unfinished.requests.isEmpty && !arithmetic.isEmpty do
    throwError "open reader discovery lost support or arithmetic obligations"
  let generalized ← withLocalDeclD `p (mkSort .zero) fun proposition =>
    withLocalDeclD `h proposition fun hypothesis =>
      FiniteData.collectSupport 0 #[] (fun _ => pure proposition)
        (fun type => do
          if ← isDefEq type proposition then return some hypothesis
          return none)
        (fun _ _ => throwError "hypothesis abstraction invoked a producer")
  let .complete closedType closedProof := generalized.result
    | throwError "local proof did not close"
  if closedType.hasFVar || closedProof.hasFVar then throwError "local proof escaped its context"
  let expected ← Elab.Term.elabType (← `(∀ p : Prop, p → p))
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq closedType expected do throwError "local proof dropped its hypothesis"
  kernelCheck `__finiteSupportHypothesis closedType closedProof
  logInfo "finite transport collected exact packing/sign support; cached replay and wrong-key rejection checked"

end Hex.RealClosure.Algebraic.KernelReplay.FiniteSupportProbe
end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
/-- info: finite transport collected exact packing/sign support; cached replay and wrong-key rejection checked -/
#guard_msgs in
#finite_support_probe

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteSupportProbe.productData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteSupportProbe.productData
