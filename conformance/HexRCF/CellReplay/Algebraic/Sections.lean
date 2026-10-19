/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Inputs
import HexRCF.RealCoefficients.CellRead
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Sections
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open Schema Inputs
open Lean Meta Elab Command Term
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
abbrev Table (facts : List (Algebraic.SignFact Data.native)) :=
  @RootTable.Result parent.Value Signature _ _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    parent.sign parent.signature (Inputs.polynomialAt facts) .negInf .posInf

def rootList (facts : List (Algebraic.SignFact Data.native)) (table : Table facts) :=
  @RootTable.Result.roots parent.Value Signature _ _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    parent.sign parent.signature (Inputs.polynomialAt facts) .negInf .posInf table

abbrev Rows (facts : List (Algebraic.SignFact Data.native)) :=
  Sigma fun table : Table facts => ((i : Fin (rootList facts table).length) →
    @SelectedSigns parent.Value Signature _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    _ parent.sign parent.signature ((rootList facts table).get i) (queriesAt facts))

def readAll (facts : List (Algebraic.SignFact Data.native)) : Except Replay.Error (Rows facts) := do
  let table ← tableAt facts
  let fields ← match Codec.tuple (rootList facts table).length Literals.sections with
    | .error _ => .error .evidence
    | .ok fields => .ok fields
  let rows ← CellRead.collect (fun i =>
    @SelectedSigns parent.Value Signature _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    _ parent.sign parent.signature ((rootList facts table).get i) (queriesAt facts)) (fun i =>
    @RowOperations.read parent.Value Signature _ _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
      (Algebraic.Element.signCodec Data.base.codec facts) Signature.codec parent.sign parent.signature
      ((rootList facts table).get i) (queriesAt facts) fields[i])
  return ⟨table, rows⟩

end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Sections
