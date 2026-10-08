/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SelectedRoot.Controls
public import HexRealClosure.ReplayOperations

public section

open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests Hex.RCF.SelectedRootTests.Data Hex.RCF.SelectedRootTests.Upper
/-! Original-packing operations for the selected-row regression.
Records preserve original request identity and control finite replay progress;
operation agreement gives the same row semantics for every valid inventory.
This inventory covers row arithmetic. Source coefficients use authenticated
`Element.restore`; upper-descriptor and row-packet reconstruction still use
the existing checked scalar-fact inventories. -/

namespace Hex.RCF.SelectedRootTests.Packing

def readRecord (original kept : Codec.Json) (claimed : Int)
    (scalar joint : Codec.Json) : Option (Algebraic.Packing native) := do
  let p ← (Codec.readPoly base.codec original).toOption
  let fact ← Read.fromPacket? kept claimed scalar
  let graph ← (Codec.readGraph base.codec Tower.Signature.codec base.signature
    native.root.raw.head native.root.raw.lower native.root.raw.upper joint).toOption
  let memo ← graph.validate? base.sign base.signature native.root.raw.head
    native.root.raw.lower native.root.raw.upper
  Algebraic.Packing.readMemo? reduction reduction_eq [fact] p memo graph.root


def evaluate (entries : List (Algebraic.Packing native)) :=
  SelectedFormula.checkRowWith original values [] schema context
    (Algebraic.Element.replayOne (context := native) inferInstance rfl entries)
    (Algebraic.Element.replayAdd (context := native) inferInstance rfl entries)
    (Algebraic.Element.replayNeg (context := native) inferInstance rfl entries)
    (Algebraic.Element.replaySub (context := native) inferInstance rfl entries)
    (Algebraic.Element.replayMul (context := native) inferInstance inferInstance rfl rfl entries)
    (Algebraic.Element.replayInv (context := native) inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance rfl rfl rfl rfl rfl rfl entries)
    (Algebraic.Element.replayDiv (context := native) inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance rfl rfl rfl rfl rfl rfl entries)
    (Algebraic.Element.replayNatCast (context := native) inferInstance rfl entries)
    (Algebraic.Element.replayOne_eq (context := native) inferInstance rfl entries)
    (Algebraic.Element.replayAdd_eq (context := native) inferInstance rfl entries)
    (Algebraic.Element.replayNeg_eq (context := native) inferInstance rfl entries)
    (Algebraic.Element.replaySub_eq (context := native) inferInstance rfl entries)
    (Algebraic.Element.replayMul_eq (context := native) inferInstance inferInstance rfl rfl entries)
    (Algebraic.Element.replayInv_eq (context := native) inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance rfl rfl rfl rfl rfl rfl entries)
    (Algebraic.Element.replayDiv_eq (context := native) inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance rfl rfl rfl rfl rfl rfl entries)
    (Algebraic.Element.replayNatCast_eq (context := native) inferInstance rfl entries)
    Controls.packet

def program (entries : List (Algebraic.Packing native)) : Bool :=
  match evaluate entries with
  | .ok true => true
  | _ => false

theorem evaluate_eq (entries : List (Algebraic.Packing native)) :
    evaluate entries = SelectedFormula.checkRow original values [] schema context Controls.packet := by
  unfold evaluate
  apply SelectedFormula.checkRowWith_eq

theorem checked (entries : List (Algebraic.Packing native)) (accepted : program entries = true) :
    SelectedFormula.checkRow original values [] schema context Controls.packet = .ok true := by
  have result : evaluate entries = .ok true := by
    unfold program at accepted
    cases h : evaluate entries with
    | error error => rw [h] at accepted; contradiction
    | ok value =>
      cases value with
      | false => rw [h] at accepted; contradiction
      | true => rfl
  exact (evaluate_eq entries).symm.trans result

theorem source (entries : List (Algebraic.Packing native)) (accepted : program entries = true) :
    ∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by
  obtain ⟨x, truth⟩ := SelectedFormula.row_sound original values [] schema context Controls.packet
    (checked entries accepted)
  exact ⟨x, (Source.schema_real x).mp truth⟩
end Hex.RCF.SelectedRootTests.Packing
