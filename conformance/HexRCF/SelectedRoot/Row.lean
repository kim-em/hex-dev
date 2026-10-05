/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.Upper
import HexRCF.RealCoefficients.SelectedFormula
import HexRealClosure.SignEvidence

open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests.Data Hex.RCF.SelectedRootTests.Upper
namespace Hex.RCF.SelectedRootTests.Row
open Hex.RCF.SelectedRootTests

def packetRead (facts : List (Algebraic.SignFact native)) :=
  (Algebraic.SignEvidence.codec (Algebraic.Element.signCodec base.codec facts)
    Tower.Signature.codec raw).decode Literals.rowPacket

def evaluateAt (root : Descriptor parent.Value Tower.Signature parent.sign parent.signature)
    (facts : List (Algebraic.SignFact native))
    (coefficients : Fin 1 → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF 2) (packet : Algebraic.SignEvidence parent.Value Tower.Signature) :
    Except Hex.RCF.RealCoefficients.Replay.Error Bool :=
  SelectedFormula.checkRowWith original coefficients guards formula (Algebraic.Context.adjoin root parent.isClean)
      (Algebraic.Element.cachedOne reduction reduction_eq facts)
      (Algebraic.Element.cachedAdd reduction reduction_eq facts)
      (Algebraic.Element.cachedNeg reduction reduction_eq facts)
      (Algebraic.Element.cachedSub reduction reduction_eq facts)
      (Algebraic.Element.cachedMul reduction reduction_eq facts)
      (Algebraic.Element.cachedInv reduction reduction_eq facts)
      (Algebraic.Element.cachedDiv reduction reduction_eq facts)
      (Algebraic.Element.cachedNatCast reduction reduction_eq facts)
      (by exact Algebraic.Element.cachedOne_eq reduction reduction_eq facts)
      (by exact Algebraic.Element.cachedAdd_eq reduction reduction_eq facts)
      (by exact Algebraic.Element.cachedNeg_eq reduction reduction_eq facts)
      (by exact Algebraic.Element.cachedSub_eq reduction reduction_eq facts)
      (by exact Algebraic.Element.cachedMul_eq reduction reduction_eq facts)
      (by exact Algebraic.Element.cachedInv_eq reduction reduction_eq facts)
      (by exact Algebraic.Element.cachedDiv_eq reduction reduction_eq facts)
      (by exact Algebraic.Element.cachedNatCast_eq reduction reduction_eq facts)
      packet

def evaluate (facts : List (Algebraic.SignFact native))
    (coefficients : Fin 1 → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF 2) (packet : Algebraic.SignEvidence parent.Value Tower.Signature) :=
  evaluateAt Upper.root facts coefficients guards formula packet

theorem evaluate_eq (facts : List (Algebraic.SignFact native))
    (coefficients : Fin 1 → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF 2) (packet : Algebraic.SignEvidence parent.Value Tower.Signature) :
    evaluate facts coefficients guards formula packet =
      SelectedFormula.checkRow original coefficients guards formula context packet := by
  unfold evaluate evaluateAt
  erw [SelectedFormula.checkRowWith_eq]
  rfl

def rowResult (facts : List (Algebraic.SignFact native)) :
    Except Hex.RCF.RealCoefficients.Replay.Error Bool :=
  match packetRead facts with
  | .error _ => .error .evidence
  | .ok packet => evaluate facts values [] schema packet

theorem root_raw (root : Descriptor parent.Value Tower.Signature parent.sign parent.signature) :
    (Algebraic.Context.adjoin root parent.isClean).root.raw = root.raw := rfl

def rowProgramAt (root : Descriptor parent.Value Tower.Signature parent.sign parent.signature)
    (facts : List (Algebraic.SignFact native)) : Bool :=
  match packetRead facts with
  | .error _ => false
  | .ok packet => match evaluateAt root facts values [] schema packet with
    | .ok true => true
    | _ => false

def rowProgram (facts : List (Algebraic.SignFact native)) : Bool :=
  match rowResult facts with
  | .ok true => true
  | _ => false

end Hex.RCF.SelectedRootTests.Row
