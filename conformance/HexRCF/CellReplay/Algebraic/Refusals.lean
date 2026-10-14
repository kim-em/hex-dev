/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Canonical
import HexRCF.CellReplay.Algebraic.Mutations
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Refusals
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open Schema Inputs Sections
open Lean Meta Elab Command Term
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Decode against the actual cached root table, with an independently supplied
literal inventory. The first sector has no left boundary. -/
def read (facts : List (Algebraic.SignFact Data.native)) (data : Read.Sectors facts)
    (decodeFacts : List (Algebraic.SignFact Data.native)) (packet : Codec.Json) : Except Replay.Error Bool :=
  let roots := rootList facts data.1.1
  let cut : Fin (roots.length+1) := ⟨0, Nat.zero_lt_succ _⟩
  (@CellPacketRead.read parent.Value Signature _ _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.signCodec Data.base.codec decodeFacts) Signature.codec parent.sign parent.signature []
    roots cut (queriesAt facts) packet).map (fun _ => true)

def hasError (actual : Except Replay.Error Bool) (expected : Replay.Error) : Bool :=
  match actual with
  | .error error => Decidable.decide (error = expected)
  | .ok _ => false

/-- A section is bound to its actual selected conjugate, even when both
roots have the same matrix signs. -/
def readSection (facts : List (Algebraic.SignFact Data.native)) (data : Read.Sectors facts)
    (packet : Codec.Json) : Except Replay.Error Bool :=
  match rootList facts data.1.1 with
  | [] => .error .evidence
  | first :: _ =>
    (@RowOperations.read parent.Value Signature _ _ _
      (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
      (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
      (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
      (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
      (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
      (Algebraic.Element.signCodec Data.base.codec facts) Signature.codec parent.sign parent.signature
      first (queriesAt facts) packet).map (fun _ => true)

def conjugates : Bool :=
  match Codec.tuple 2 Literals.sections with
  | .error _ => false
  | .ok rows =>
    (readSection Canonical.facts Canonical.data rows[0] == .ok true) &&
    hasError (readSection Canonical.facts Canonical.data rows[1]) .evidence

def controls : Bool :=
  let facts := Canonical.facts
  let data := Canonical.data
  let fields := (Codec.tuple 3 Literals.sectors).toOption
  match fields with
  | none => false
  | some fields =>
    (read facts data facts fields[0] == .ok true) &&
    hasError (read facts data facts Mutations.wrongPoint) .binding &&
    hasError (read facts data facts Mutations.presentLeft) .binding &&
    hasError (read facts data facts Mutations.absentRight) .evidence &&
    hasError (read facts data facts Mutations.otherRoot) .binding &&
    hasError (read facts data facts Mutations.staleContext) .evidence &&
    hasError (read facts data [] fields[0]) .evidence && conjugates

elab "#algebraic_packet_refusals" : command => liftTermElabM do
  let type ← mkEq (Lean.mkConst ``controls) (Lean.mkConst ``Bool.true)
  let decision ← mkDecide type
  let mut rules ← RowTools.rules
  for name in #[``controls, ``conjugates, ``readSection, ``read, ``hasError, ``Read.readAll, ``Sections.readAll,
      ``rootList, ``Inputs.tableAt, ``Inputs.queriesAt, ``Inputs.polynomialAt,
      ``RootTable.read, ``RootTable.extract, ``Schema.values, ``Schema.atom, ``Schema.formula,
      ``RowOperations.read, ``CellPacketRead.read, ``CellRead.collect,
      ``Algebraic.RootReplay.readDescriptor, ``Descriptor.ofChecked] do
    rules ← rules.addDeclToUnfold name
  let context ← Simp.mkContext (simpTheorems := #[rules]) (congrTheorems := ← getSimpCongrTheorems)
  let (outcome, _) ← Algebraic.KernelReplay.assemble decision context
  match outcome with
  | .checked true proof _ =>
    let proof ← mkAppM ``of_decide_eq_true #[proof]
    KernelCheck.addChecked `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Refusals.accepted
      type proof #[``Descriptor.ofReplay?] #[``CellPacketRead.read]
  | .checked false .. => throwError "algebraic packet controls failed"
  | .missing request => throwError "algebraic packet controls lack {request}"
#algebraic_packet_refusals
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Refusals
