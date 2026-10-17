/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Sections
import HexRCF.CellReplay.Algebraic.Records
import HexRCF.RealCoefficients.CellPacketRead
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Read
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open Schema Inputs Sections
open Lean Meta Elab Command Term
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
abbrev Sectors (facts : List (Algebraic.SignFact Data.native)) :=
  Sigma fun sections : Rows facts => ((cut : Fin ((rootList facts sections.1).length+1)) →
    @CellPackets.Sector parent.Value Signature _ _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    parent.sign parent.signature (rootList facts sections.1) cut (queriesAt facts))

def readAll (facts : List (Algebraic.SignFact Data.native)) : Except Replay.Error (Sectors facts) := do
  let sections ← Sections.readAll facts
  let fields ← match Codec.tuple ((rootList facts sections.1).length+1) Literals.sectors with
    | .error _ => .error .evidence
    | .ok fields => .ok fields
  let sectors ← CellRead.collect (fun cut =>
    @CellPackets.Sector parent.Value Signature _ _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    parent.sign parent.signature (rootList facts sections.1) cut (queriesAt facts)) (fun cut =>
    @CellPacketRead.read parent.Value Signature _ _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
      (Algebraic.Element.signCodec Data.base.codec facts) Signature.codec parent.sign parent.signature []
      (rootList facts sections.1) cut (queriesAt facts) fields[cut])
  return ⟨sections, sectors⟩

abbrev facts := Records.facts
elab "#algebraic_sectors_check" : command => liftTermElabM do
  let program ← mkAppM ``readAll #[Lean.mkConst ``facts]
  let type ← mkEq (← mkAppM ``Option.isSome #[← mkAppM ``Except.toOption #[program]]) (Lean.mkConst ``Bool.true)
  let decision ← mkDecide type
  let mut rules ← RowTools.rules
  for name in #[``readAll, ``Sections.readAll, ``Sections.rootList,
      ``Inputs.tableAt, ``Inputs.queriesAt, ``Inputs.polynomialAt,
      ``RootTable.read, ``RootTable.extract, ``Schema.values,
      ``Schema.atom, ``Schema.formula,
      ``RowOperations.read, ``CellPacketRead.read, ``CellPacketRead.readUsing, ``CellRead.collect,
      ``Algebraic.RootReplay.readDescriptor, ``Descriptor.ofChecked] do
    rules ← rules.addDeclToUnfold name
  let context ← Simp.mkContext (simpTheorems := #[rules]) (congrTheorems := ← getSimpCongrTheorems)
  let (outcome, _) ← Algebraic.KernelReplay.assemble decision context
  match outcome with
  | .checked true proof _ =>
    let proof ← mkAppM ``of_decide_eq_true #[proof]
    KernelCheck.addChecked `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Read.accepted type proof #[``Descriptor.ofReplay?]
      #[``readAll, ``CellPacketRead.read]
  | .checked false .. => throwError "complete algebraic sectors rejected"
  | .missing request => throwError "frozen complete algebraic sectors lack {request}"
#algebraic_sectors_check
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Read
