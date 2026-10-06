/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.RealCoefficients.SelectedBytes
import HexRCF.SelectedRoot.ByteBounds
import HexRCF.SelectedRoot.Checks
import HexRCF.Tactic

open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests.Data Hex.RCF.SelectedRootTests.Upper
namespace Hex.RCF.SelectedRootTests.ByteProofs
open Hex.RCF.SelectedRootTests

def facts := RowCollect.facts
def valueCodec := Algebraic.Element.signCodec base.codec facts
def bytes := Hex.RCF.SelectedRootTests.ByteData.literal

theorem bounded : Codec.checkBytes {} bytes = .ok () := Hex.RCF.SelectedRootTests.ByteBounds.bounded

theorem packetJSON : Row.packetRead facts = .ok Controls.packet := by
  have read : (Row.packetRead facts).toOption = some Controls.packet :=
    (Option.some_get Controls.packetAccepted).symm
  cases h : Row.packetRead facts with
  | error message => simp only [h, Except.toOption] at read; contradiction
  | ok packet =>
    simp only [h, Except.toOption] at read
    exact congrArg Except.ok (Option.some.inj read)

theorem decoded : (SelectedFormula.packetCodec context valueCodec Tower.Signature.codec).decodeBytes
    bytes {} = .ok Controls.packet := by
  have guarded : Codec.checkBytes {} Literals.rowPacket.writeBytes = .ok () := by
    rw [Hex.RCF.SelectedRootTests.ByteData.written]
    exact bounded
  unfold ValueCodec.decodeBytes bytes
  rw [← Hex.RCF.SelectedRootTests.ByteData.written, Codec.parse_write Literals.rowPacket {} guarded]
  change Row.packetRead facts = .ok Controls.packet
  exact packetJSON

theorem rowChecked : SelectedFormula.checkRow original values [] schema context Controls.packet = .ok true := by
  have accepted := Proofs.rowAccepted
  unfold Row.rowResult at accepted
  change (match Row.packetRead facts with
    | .error _ => Except.error Replay.Error.evidence
    | .ok packet => Row.evaluate facts values [] schema packet) = .ok true at accepted
  rw [packetJSON] at accepted
  exact (Row.evaluate_eq facts values [] schema Controls.packet) ▸ accepted

theorem bytesAccepted : SelectedFormula.checkBytes original values [] schema context
    valueCodec Tower.Signature.codec bytes {} = .ok (.ok true) := by
  rw [SelectedFormula.bytes_decoded original values [] schema context
    valueCodec Tower.Signature.codec bytes {} Controls.packet decoded, rowChecked]

theorem exists_nested : ∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by
  obtain ⟨x, truth⟩ := SelectedFormula.bytes_sound original values [] schema context
    valueCodec Tower.Signature.codec bytes {} bytesAccepted
  exact ⟨x, (Source.schema_real x).mp truth⟩

theorem zeroFirst : SelectedFormula.checkBytes original values [Controls.zeroGuard] schema context
    valueCodec Tower.Signature.codec bytes {bytes := 0} = .ok (.error .divisor) := by
  have zero : Controls.zeroGuard = 0 := (original.zero_iff _).mp (by
    rw [Checks.zero_real]; exact sub_self _)
  apply SelectedFormula.bytes_zero
  simp [zero]

/-- info: 'Hex.RCF.SelectedRootTests.ByteProofs.exists_nested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_nested

end Hex.RCF.SelectedRootTests.ByteProofs
