/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.Facts
import HexRCF.NestedTransport.Operations
import HexRCF.SelectedRoot.KernelCheck
import HexRCF.SelectedRoot.RowTools
import Lean.Elab.Command
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.RealCoefficients.NestedTransportTests.RootRead
open Hex.RCF.RealCoefficients.NestedTransportTests.Context
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
def readAt (facts : List (Algebraic.SignFact native))
    (prior : List (Algebraic.SignFact Data.native)) :=
  @Algebraic.RootReplay.readDescriptor target.Value Signature
    (Tower.instZeroValue target) (Tower.instDecidableEqValue target) inferInstance
    (Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherOne facts prior)
    (Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherAdd facts prior)
    (Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherSub facts prior)
    (Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherMul facts prior)
    (Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherNat facts prior)
    (Algebraic.Element.signCodec (Algebraic.Element.signCodec Data.base.codec prior) facts)
    Signature.codec target.sign target.signature Hex.RCF.RealCoefficients.NestedTransportTests.Literals.subject Hex.RCF.RealCoefficients.NestedTransportTests.Literals.graph

meta section
open Lean Meta Elab Command
elab "#suffix_literal_root_check" : command => liftTermElabM do
  let result ← mkAppM ``readAt #[mkConst ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.facts, mkConst ``Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts]
  let proposition ← mkEq (← mkAppM ``Option.isSome #[← mkAppM ``Except.toOption #[result]])
    (mkConst ``Bool.true)
  let dictionary ← synthInstance (mkApp (mkConst ``Decidable) proposition)
  let decision := mkAppN (mkConst ``Decidable.decide) #[proposition,dictionary]
  let mut rules ← RowTools.rules
  for name in #[``readAt, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.facts,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.first, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.second,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.third, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.fourth,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.fifth,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.fact, ``Hex.RCF.RealCoefficients.NestedTransportTests.Restore.restore,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.polynomials, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.evidence,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.parsed, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.parsedAt, ``Hex.RCF.RealCoefficients.NestedTransportTests.Constants.constant] do
    rules ← rules.addDeclToUnfold name
  rules ← rules.addConst ``Hex.RCF.RealCoefficients.NestedTransportTests.Context.signature_eq
  rules ← rules.addConst ``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.policy
  for name in #[``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.reduce, ``Algebraic.Context.factReduce,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherOne, ``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherAdd,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherSub, ``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherMul,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherNat] do
    rules ← rules.addDeclToUnfold name
  let context ← Simp.mkContext (simpTheorems := #[rules]) (congrTheorems := ← getSimpCongrTheorems)
  let (outcome, _) ← Algebraic.KernelReplay.assemble decision context
  match outcome with
  | .checked true proof _ =>
    let proof := mkAppN (mkConst ``of_decide_eq_true) #[proposition,dictionary,proof]
    KernelCheck.addChecked `Hex.RCF.RealCoefficients.NestedTransportTests.RootRead.accepted proposition proof
      #[``Descriptor.validate, ``Descriptor.ofReplay?]
  | .checked false .. => throwError "supplied descriptor rejected"
  | .missing app =>
    let request ← Algebraic.KernelReplay.request app
    let kind := match request.kind with
      | .coefficient => "coefficient"
      | .valueSign => "valueSign"
      | .inverse => "inverse"
    let key ← withOptions (fun o => smartUnfolding.set o false) do
      withTransparency .all (reduce request.polynomial)
    logInfo m!"missing kind={kind}; context={request.context}; reduced polynomial={key}"
    throwError "descriptor needs a reached coefficient record"
end
#suffix_literal_root_check
end Hex.RCF.RealCoefficients.NestedTransportTests.RootRead
