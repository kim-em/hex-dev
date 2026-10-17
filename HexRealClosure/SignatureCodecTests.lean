/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerContext

public section
namespace Hex.RealClosure.Tower.SignatureCodecTests
open Hex.SignDet

@[expose] def signature : Signature := ⟨⟨[], 0⟩, []⟩

@[expose] def packet : Codec.Json :=
  .array (.cons (.array .nil) (.cons (.number 0) (.cons (.array .nil) .nil)))

/-- An ordinary importer can identify a frozen full-signature packet. -/
theorem encode : Signature.codec.encode signature = packet := by
  rw [Signature.codec_encode]
  rfl

theorem decode : Signature.codec.decode packet = .ok signature := by
  have literal : packet = signature.literal.toJson := rfl
  rw [literal]
  exact Signature.codec_literal signature

/-- The same public decoder equation applies to arbitrary full signatures. -/
theorem frozen (source : Signature) (data : Codec.Json)
    (literal : data = source.literal.toJson) :
    Signature.codec.decode data = .ok source := by
  rw [literal]
  exact Signature.codec_literal source

/-- info: 'Hex.RealClosure.Tower.Signature.codec_encode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Signature.codec_encode

/-- info: 'Hex.RealClosure.Tower.Signature.codec_literal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Signature.codec_literal

/-- info: 'Hex.RealClosure.Tower.SignatureCodecTests.encode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms encode

/-- info: 'Hex.RealClosure.Tower.SignatureCodecTests.decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decode

/-- info: 'Hex.RealClosure.Tower.SignatureCodecTests.frozen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frozen

end Hex.RealClosure.Tower.SignatureCodecTests
