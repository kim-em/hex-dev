/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.BooleanSources
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet Hex.RealFormula
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open Hex.RCF.RealCoefficients.CellReplayTests.Algebraic
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.BooleanBinding
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def reordered : QF 2 := .and (.atom ⟨0, .eq⟩)
  (.and (.atom ⟨Schema.atom, .ge⟩) (.atom ⟨Schema.atom, .le⟩))

def queriesAt (facts : List (Algebraic.SignFact Data.native)) :=
  @RepresentationSpecialize.prepare Schema.parent.Value _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNeg Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts) _ Schema.values reordered

def read (facts : List (Algebraic.SignFact Data.native)) (data : Read.Sectors facts) : Except Replay.Error Bool := do
  let first ← match Sections.rootList facts data.1.1 with
    | [] => .error .evidence
    | first :: _ => .ok first
  let rows ← match Codec.tuple 2 Literals.sections with
    | .error _ => .error .evidence
    | .ok rows => .ok rows
  (@RowOperations.read Schema.parent.Value Signature _ _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.signCodec Data.base.codec facts) Signature.codec Schema.parent.sign
    Schema.parent.signature first (queriesAt facts) rows[0]).map (fun _ => true)

open Lean Meta Elab Command Term
elab "#reordered_formula_refused" : command => liftTermElabM do
  let actual ← mkAppM ``read #[Lean.mkConst ``Canonical.facts, Lean.mkConst ``Canonical.data]
  let expected ← mkAppOptM ``Except.error #[some (Lean.mkConst ``Replay.Error),some (Lean.mkConst ``Bool),some (Lean.mkConst ``Replay.Error.binding)]
  let type ← mkEq actual expected
  let decision ← mkDecide type
  let mut rules ← RowTools.rules
  for name in #[``read, ``queriesAt, ``reordered, ``Read.readAll, ``Sections.readAll,
      ``Sections.rootList, ``Inputs.tableAt, ``Inputs.queriesAt, ``Inputs.polynomialAt,
      ``RootTable.read, ``RootTable.extract, ``Schema.values, ``Schema.atom, ``Schema.formula,
      ``RowOperations.read, ``CellPacketRead.read, ``CellRead.collect,
      ``Algebraic.RootReplay.readDescriptor, ``Descriptor.ofChecked] do
    rules ← rules.addDeclToUnfold name
  let context ← Simp.mkContext (simpTheorems := #[rules]) (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← Algebraic.KernelReplay.assemble decision context
  match result with
  | .checked true proof _ =>
    let proof ← mkAppM ``of_decide_eq_true #[proof]
    KernelCheck.addChecked `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.BooleanBinding.refused type proof
      #[``Descriptor.ofReplay?] #[``RowOperations.read]
  | .checked false .. => throwError "reordered formula packet was not refused"
  | .missing request => throwError "reordered formula refusal lacks {request}"
#reordered_formula_refused
#print axioms refused
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.BooleanBinding
