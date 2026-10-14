/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Canonical
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Radical
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients Schema
open Lean Meta Elab Command Term
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def checkAt (facts : List (Algebraic.SignFact Data.native)) : Bool :=
  @RadicalCert.check parent.Value Signature _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts) _ parent.signature
    (@RepresentationCarrier.product parent.Value _ _
      (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
      (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
      (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
      (Inputs.queriesAt facts)) Canonical.cert

theorem checkOps {E Ctx : Type} [Zero E] [DecidableEq E]
    [one : One E] [add : Add E] [sub : Sub E] [mul : Mul E]
    [DecidableEq Ctx] (otherOne : One E) (otherAdd : Add E) (otherSub : Sub E) (otherMul : Mul E)
    (ho : otherOne = one) (ha : otherAdd = add) (hs : otherSub = sub) (hm : otherMul = mul)
    (context : Ctx) (queries after : List (DensePoly E)) (same : queries = after)
    (cert : RadicalCert E Ctx) :
    @RadicalCert.check E Ctx _ _ otherOne otherAdd otherSub otherMul _ context
      (@RepresentationCarrier.product E _ _ otherOne otherAdd otherMul queries) cert =
      @RadicalCert.check E Ctx _ _ one add sub mul _ context
        (@RepresentationCarrier.product E _ _ one add mul after) cert := by
  cases same; cases ho; cases ha; cases hs; cases hm
  rfl


theorem checkAt_eq (facts : List (Algebraic.SignFact Data.native)) :
    checkAt facts = Canonical.cert.check parent.signature
      (RepresentationCarrier.product (RepresentationSpecialize.prepare values formula)) := by
  exact @checkOps parent.Value Signature
    (Tower.instZeroValue parent) (Tower.instDecidableEqValue parent)
    (Tower.instOneValue parent) (Tower.instAddValue parent) (Tower.instSubValue parent)
    (Tower.instMulValue parent) inferInstance
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedOne_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul_eq Data.reduction Data.reduction_eq facts)
    parent.signature (Inputs.queriesAt facts)
    (RepresentationSpecialize.prepare values formula) (Convert.queries_eq facts)
    Canonical.cert


abbrev facts := Read.facts
elab "#algebraic_radical_check" : command => liftTermElabM do
  let check ← mkAppM ``checkAt #[Lean.mkConst ``facts]
  let type ← mkEq check (Lean.mkConst ``Bool.true)
  let decision ← mkDecide type
  let mut rules ← RowTools.rules
  for name in #[``checkAt, ``Inputs.queriesAt, ``Inputs.polynomialAt,
      ``Schema.values, ``Schema.atom, ``Schema.formula,
      ``RepresentationCarrier.product, ``RadicalCert.check] do
    rules ← rules.addDeclToUnfold name
  let context ← Simp.mkContext (simpTheorems := #[rules]) (congrTheorems := ← getSimpCongrTheorems)
  let (outcome, _) ← Algebraic.KernelReplay.assemble decision context
  match outcome with
  | .checked true proof _ =>
    let proof ← mkAppM ``of_decide_eq_true #[proof]
    KernelCheck.addChecked `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Radical.accepted type proof #[``Descriptor.ofReplay?]
      #[``checkAt, ``RadicalCert.check]
  | .checked false .. => throwError "algebraic radical rejected"
  | .missing request => throwError "frozen algebraic radical lacks {request}"
#algebraic_radical_check

theorem checked : Canonical.cert.check parent.signature
    (RepresentationCarrier.product (RepresentationSpecialize.prepare values formula)) = true :=
  (checkAt_eq facts).symm.trans accepted
#print axioms checked
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Radical
