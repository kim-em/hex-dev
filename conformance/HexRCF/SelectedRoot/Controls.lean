/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.Proofs
import HexRealClosure.SignEvidence

open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests.Data Hex.RCF.SelectedRootTests.Upper
namespace Hex.RCF.SelectedRootTests.Controls
open Hex.RCF.SelectedRootTests

def facts := RowCollect.facts

theorem packetAccepted : (Row.packetRead facts).toOption.isSome = true := by
  have accepted := Proofs.rowAccepted
  change Row.rowResult facts = .ok true at accepted
  unfold Row.rowResult at accepted
  cases packet : Row.packetRead facts with
  | error message => simp only [packet] at accepted; contradiction
  | ok evidence => rfl

def packet : Algebraic.SignEvidence parent.Value Tower.Signature :=
  (Row.packetRead facts).toOption.get packetAccepted

def falseSchema : RealFormula.QF 2 :=
  let x : RealFormula.Poly 2 := MvPoly.X 1
  .and (.atom ⟨x^2-MvPoly.X 0, .ne⟩)
    (.and (.atom ⟨x-1, .gt⟩) (.atom ⟨x-2, .lt⟩))

def negative : parent.Value :=
  @Neg.neg parent.Value (Algebraic.Element.cachedNeg reduction reduction_eq facts) alpha

def zeroGuard : parent.Value :=
  @Sub.sub parent.Value (Algebraic.Element.cachedSub reduction reduction_eq facts) alpha alpha

def badPacket : Algebraic.SignEvidence parent.Value Tower.Signature :=
  {queries := [], values := ⟨#[], rfl⟩, graph := {entries := #[], root := 0}}

def falseProgram (inventory : List (Algebraic.SignFact native)) : Bool :=
  Decidable.decide (Row.evaluate inventory values [] falseSchema packet = .ok false)
def wrongCoefficient (inventory : List (Algebraic.SignFact native)) : Bool :=
  Decidable.decide (Row.evaluate inventory (fun _ => negative) [] schema packet = .error .evidence)
def swappedKeys (inventory : List (Algebraic.SignFact native)) : Bool :=
  let evidence : Algebraic.SignEvidence parent.Value Tower.Signature := {
    queries := packet.queries.reverse
    values := ⟨packet.values.toArray.reverse, by simp⟩
    graph := packet.graph }
  Decidable.decide (Row.evaluate inventory values [] schema evidence = .error .evidence)

def forgedRow (inventory : List (Algebraic.SignFact native)) : Bool :=
  let evidence : Algebraic.SignEvidence parent.Value Tower.Signature := {
    queries := packet.queries
    values := ⟨packet.values.toArray.set! 0 1, by simp⟩
    graph := packet.graph }
  Decidable.decide (Row.evaluate inventory values [] schema evidence = .error .evidence)

def zeroBeforePacket : Bool :=
  Decidable.decide (Row.evaluate facts values [zeroGuard] schema badPacket = .error .divisor)

private def read (j : Codec.Json) :=
  (Algebraic.SignEvidence.codec (Algebraic.Element.signCodec base.codec facts)
    Tower.Signature.codec raw).decode j
private def replace (j : Codec.Json) (index : Nat) (value : Codec.Json) :=
  Codec.Json.arr ((j.getArr?.toOption.getD #[]).set! index value)

def staleVersion : Bool :=
  !(read (replace Literals.rowPacket 0 (Codec.Json.of (2 : Nat)))).isOk

def forgedSign : Bool :=
  (Read.fromPacket? Packets.packet0.1
    (-Packets.packet0.2.1) Packets.packet0.2.2).isNone

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem sign_checked : forgedSign = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem zero_checked : zeroBeforePacket = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem version_checked : staleVersion = true := by decide +kernel

/-- info: 'Hex.RCF.SelectedRootTests.Controls.sign_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_checked
/-- info: 'Hex.RCF.SelectedRootTests.Controls.zero_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_checked
/-- info: 'Hex.RCF.SelectedRootTests.Controls.version_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms version_checked
end Hex.RCF.SelectedRootTests.Controls
