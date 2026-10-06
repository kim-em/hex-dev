/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.Collect
import HexSignDet.DagExpand
import Lean.Elab.Command

open Hex Hex.RealClosure Hex.SignDet
open Hex.RCF.SelectedRootTests.Data
meta section
open Hex.RCF.SelectedRootTests
open Lean Meta Elab Command
elab "#selected_parse " name:ident " := " term:term : command => liftTermElabM do
  let program ← Term.elabTerm term (some (mkConst ``Bool))
  Term.synthesizeSyntheticMVarsNoPostponing
  let program ← instantiateMVars program
  let context ← Simp.mkContext (simpTheorems := #[← ReplayTools.rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let (outcome, _) ← Algebraic.KernelReplay.assemble program context
  match outcome with
  | .checked true proof _ =>
    let type ← mkEq program (mkConst ``Bool.true)
    KernelCheck.addChecked name.getId type proof
  | .checked false .. => throwError "literal parser rejected"
  | .missing expression => throwError "parser requires arithmetic: {expression}"
end
namespace Hex.RCF.SelectedRootTests.Frozen
open Hex.RCF.SelectedRootTests

def rawRead := Algebraic.SignRequests.readRoot
  (Algebraic.Element.signCodec base.codec Collect.facts) Tower.Signature.codec
  Literals.upperSubject

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
#selected_parse Hex.RCF.SelectedRootTests.Frozen.rawAccepted := rawRead.toOption.isSome

def raw : RawDescriptor parent.Value Tower.Signature := rawRead.toOption.get rawAccepted

def graphRead := Codec.readGraph
  (Algebraic.Element.signCodec base.codec Collect.facts) Tower.Signature.codec
  frozenSignature raw.head raw.lower raw.upper Literals.upperGraph

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
#selected_parse Hex.RCF.SelectedRootTests.Frozen.graphAccepted := graphRead.toOption.isSome

def graph := graphRead.toOption.get graphAccepted

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
#selected_parse Hex.RCF.SelectedRootTests.Frozen.treeAccepted := graph.expand?.isSome

def tree := graph.expand?.get treeAccepted

def checkAt (facts : List (Algebraic.SignFact native)) (binding : Tower.Signature) : Bool :=
  @RawDescriptor.check (Algebraic.Element native) Tower.Signature _ _
    (Algebraic.Element.cachedOne reduction reduction_eq facts)
    (Algebraic.Element.cachedAdd reduction reduction_eq facts)
    (Algebraic.Element.cachedSub reduction reduction_eq facts)
    (Algebraic.Element.cachedMul reduction reduction_eq facts)
    (Algebraic.Element.cachedNatCast reduction reduction_eq facts)
    _ Algebraic.Element.sign binding raw tree

def check (facts : List (Algebraic.SignFact native)) : Bool := checkAt facts parent.signature

theorem check_frozen (facts : List (Algebraic.SignFact native)) :
    check facts = checkAt facts frozenSignature := congrArg (checkAt facts) signature_eq

theorem check_eq (facts : List (Algebraic.SignFact native)) :
    check facts = raw.check parent.sign parent.signature tree := by
  unfold check checkAt
  erw [Algebraic.Element.cachedOne_eq reduction reduction_eq facts,
    Algebraic.Element.cachedAdd_eq reduction reduction_eq facts,
    Algebraic.Element.cachedSub_eq reduction reduction_eq facts,
    Algebraic.Element.cachedMul_eq reduction reduction_eq facts,
    Algebraic.Element.cachedNatCast_eq reduction reduction_eq facts]
  rfl

end Hex.RCF.SelectedRootTests.Frozen
