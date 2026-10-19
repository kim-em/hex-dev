/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.RootRead
import HexRCF.NestedTransport.Conversion
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Read
open Hex.RCF.RealCoefficients.NestedTransportTests.Context Hex.RCF.RealCoefficients.NestedTransportTests.Operations
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
def mapped (facts : List (Algebraic.SignFact native))
    (prior : List (Algebraic.SignFact Data.native)) : Data.parent.Value → target.Value := fun a =>
  Algebraic.Element.pack (reduce prior) (reduce_eq prior) facts
    (DensePoly.ofCoeffs (a.polynomial.toArray.map
      (Hex.RCF.RealCoefficients.RootTransportData.mapped prior)))
theorem mapped_eq (facts : List (Algebraic.SignFact native))
    (prior : List (Algebraic.SignFact Data.native)) :
    mapped facts prior = Hex.RCF.RealCoefficients.NestedTransportTests.Conversion.converted.value := by
  have same : mapped facts prior = Hex.RCF.RealCoefficients.NestedTransportTests.Map.mapped facts prior := by
    funext a
    unfold mapped Hex.RCF.RealCoefficients.NestedTransportTests.Map.mapped
    exact (Algebraic.Element.pack_eq (reduce prior) (reduce_eq prior) facts _).trans
      (Algebraic.Element.pack_eq native.reduce rfl facts _).symm
  exact same.trans (Hex.RCF.RealCoefficients.NestedTransportTests.Conversion.supplied_eq facts prior)
def readFor (facts : List (Algebraic.SignFact native))
    (prior : List (Algebraic.SignFact Data.native))
    (source : Descriptor Data.parent.Value Signature Data.parent.sign Data.parent.signature)
    (guards : List Data.parent.Value) (subject graph : Codec.Json) :=
  Hex.RCF.RealCoefficients.RootTransport.readWith Hex.RCF.RealCoefficients.NestedTransportTests.Conversion.converted source
    (Algebraic.Element.signCodec (Algebraic.Element.signCodec Data.base.codec prior) facts)
    (mapped facts prior) (mapped_eq facts prior)
    (higherOne facts prior) (higherAdd facts prior) (higherSub facts prior)
    (higherMul facts prior) (higherNat facts prior)
    (higherOne_eq facts prior) (higherAdd_eq facts prior) (higherSub_eq facts prior)
    (higherMul_eq facts prior) (higherNat_eq facts prior)
    guards subject graph
def readAt facts prior :=
  readFor facts prior Upper.root [] Hex.RCF.RealCoefficients.NestedTransportTests.Literals.subject Hex.RCF.RealCoefficients.NestedTransportTests.Literals.graph
meta section
open Lean Meta Elab Command
elab "#suffix_full_check" : command => liftTermElabM do
  let result ← mkAppM ``readAt #[mkConst ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.facts,
    mkConst ``Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts]
  let proposition ← mkEq (← mkAppM ``Option.isSome #[← mkAppM ``Except.toOption #[result]])
    (mkConst ``Bool.true)
  let dictionary ← synthInstance (mkApp (mkConst ``Decidable) proposition)
  let decision := mkAppN (mkConst ``Decidable.decide) #[proposition,dictionary]
  let mut rules ← RowTools.rules
  for name in #[``readAt, ``readFor, ``Hex.RCF.RealCoefficients.RootTransport.readWith, ``mapped,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.facts, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.first,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.second, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.third,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.fourth, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.fifth,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.fact, ``Hex.RCF.RealCoefficients.NestedTransportTests.Restore.restore,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.polynomials, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.evidence,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.parsed, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.parsedAt, ``Hex.RCF.RealCoefficients.NestedTransportTests.Constants.constant,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.reduce, ``higherOne, ``higherAdd, ``higherSub, ``higherMul, ``higherNat] do
    rules ← rules.addDeclToUnfold name
  rules ← rules.addConst ``Hex.RCF.RealCoefficients.NestedTransportTests.Context.signature_eq
  let context ← Simp.mkContext (simpTheorems := #[rules]) (congrTheorems := ← getSimpCongrTheorems)
  let (outcome, _) ← Algebraic.KernelReplay.assemble decision context
  match outcome with
  | .checked true proof _ =>
    let proof := mkAppN (mkConst ``of_decide_eq_true) #[proposition,dictionary,proof]
    KernelCheck.addChecked `Hex.RCF.RealCoefficients.NestedTransportTests.Read.accepted proposition proof
      #[``Descriptor.validate, ``Descriptor.ofReplay?]
  | .checked false .. => throwError "supplied full binding rejected"
  | .missing app =>
    let request ← Algebraic.KernelReplay.request app
    logInfo m!"missing context={request.context}; polynomial={request.polynomial}"
    throwError "full binding needs a reached coefficient record"
end
#suffix_full_check
end Hex.RCF.RealCoefficients.NestedTransportTests.Read
